/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthProgramTree
public import NLAlib.Krylov.Processes.LanczosReorthRecurrence

/-!
# Lanczos with full reorthogonalization as a program: the matrix-free target

The exact matrix-free target approved by the maintainer on 2026-11-06 (design note
`docs/design/Krylov-LanczosReorth.md` §2.3). It fixes the registered oracle tree, the retained
input and every output buffer, the componentwise counts and the peak cells, for every real matrix
without a symmetry assumption; zero dimensions, zero inputs, zero requested steps and terminal
zero continuation are included. Oracle backend storage and arithmetic remain outside this access
model. The proof is in `LanczosReorthProgram.lean`.

## Main definitions

* `NLAlib.lanczosReorthOracleCount`: the componentwise count budget.
* `NLAlib.MatrixFreeLanczosReorth`: the exact matrix-free target.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

/-- **Componentwise upper operation counts** of the matrix-free tree: those of
`NLAlib.lanczosReorthCount` without the ROM reads and the stored `gemv` product, plus one load
and one one-column matrix-vector product per step. -/
noncomputable def lanczosReorthOracleCount {P ι : Type} (tag : P) (o : ι) (N q : ℕ) :
    OpCount P ι :=
  Finsupp.single (.load tag o) q + Finsupp.single (.matvec tag o) q +
  Finsupp.single (.bin tag .mul) (N + 5 * q * N + 4 * N * q * (q + 1)) +
  Finsupp.single (.bin tag .add) (N + 5 * q * N + (4 * N + 1) * q * (q + 1)) +
  Finsupp.single (.un tag .conj) (N + 3 * q * N + 2 * N * q * (q + 1)) +
  Finsupp.single (.bin tag .div) (N * (q + 1)) +
  Finsupp.single (.un tag .sqrt) (2 * q + 1) +
  Finsupp.single (.un tag .neg) (2 * q) +
  Finsupp.single (.lit tag) (2 * N + 3 + q * (N + 2) + 2 * q * (N + q + 2)) +
  Finsupp.single (.cmp tag) (q + 1) +
  Finsupp.single (.copy tag) (N + 2 * q * N)

/-- The exact matrix-free target: for all real matrices and inputs, the compiled oracle tree
retains the input and computes every basis column, the coefficients $\alpha_j$, $\beta_j$, the
input norm, the final previous vector and the norms $\nu_{j+1}$ of `NLAlib.lanczosReorthState`
within the displayed counts and workspace. No symmetry, nonzero-input or nonbreakdown premise is
imposed. -/
def MatrixFreeLanczosReorth : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P) (o : ι),
    MatrixFree (𝕜 := ℝ) tag (lanczosReorthOracleProg.compiled tag o)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N q b => ![(Array.ofFn b).map some, Array.replicate (N * (q 0 + 1)) none,
        Array.replicate (q 0) none, Array.replicate (q 0 + 1) none,
        Array.replicate 1 none, Array.replicate N none, Array.replicate (q 0) none])
      (fun N q => lanczosReorthOracleCount tag o N (q 0))
      (fun N q p => if p = tag then N * (q 0 + 5) + 5 * q 0 + 7 else 0)
      (fun _ q b A _ st =>
        Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
        Holds st.store tag 1 0 (lanczosReorthMatrix A b (q 0 + 1)) ∧
        Holds st.store tag 2 0 (fun (j : Fin (q 0)) (_ : Fin 1) =>
          lanczosAlpha A (lanczosReorthState A b j).toLanczosState) ∧
        Holds st.store tag 3 0
          (fun (j : Fin (q 0 + 1)) (_ : Fin 1) => (lanczosReorthState A b j).beta) ∧
        st.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
        Holds st.store tag 5 0 (fun i (_ : Fin 1) => (lanczosReorthState A b (q 0)).prev i) ∧
        Holds st.store tag 6 0
          (fun (j : Fin (q 0)) (_ : Fin 1) => (lanczosReorthState A b ((j : ℕ) + 1)).nu))

end NLAlib
