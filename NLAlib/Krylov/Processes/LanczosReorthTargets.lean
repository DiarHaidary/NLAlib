/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthProgramTree
public import NLAlib.Krylov.Processes.LanczosReorthRecurrence

/-!
# Lanczos with full reorthogonalization as a program: the stored-matrix target

The exact stored-entry target approved by the maintainer on 2026-11-06 (design note
`docs/design/Krylov-LanczosReorth.md` §2.3). It fixes the registered tree, the declared inputs,
all promised output cells, and the componentwise count and ROM-inclusive memory bounds. Like
`NLAlib.StoredEntriesLanczos` it has no symmetry, nonzero-input or nonbreakdown premise: the
specification is the exact recurrence `NLAlib.lanczosReorthState`. The proof is in
`LanczosReorthProgram.lean`.

## Main definitions

* `NLAlib.lanczosReorthCount`: the componentwise upper count formula.
* `NLAlib.StoredEntriesLanczosReorth`: the exact target of the registered implementation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

/-- **Componentwise upper operation counts** of the stored-matrix tree: `NLAlib.lanczosCount`'s
components plus, per step $j < q$, the two CGS2 passes against $j + 1$ columns ($2(j+1)$ dots and
two `gemv` of width $j + 1$, two `axpy`, one literal each), the $j + 1$ coefficient additions and
one extra `nrm2`. Each component is bounded separately. -/
noncomputable def lanczosReorthCount {P ι : Type} (tag : P) (N q : ℕ) : OpCount P ι :=
  Finsupp.single (.rom tag) (N ^ 2) +
  Finsupp.single (.bin tag .mul) (N + q * (N ^ 2 + 5 * N) + 4 * N * q * (q + 1)) +
  Finsupp.single (.bin tag .add) (N + q * (N ^ 2 + 5 * N) + (4 * N + 1) * q * (q + 1)) +
  Finsupp.single (.un tag .conj) (N + 3 * q * N + 2 * N * q * (q + 1)) +
  Finsupp.single (.bin tag .div) (N * (q + 1)) +
  Finsupp.single (.un tag .sqrt) (2 * q + 1) +
  Finsupp.single (.un tag .neg) (2 * q) +
  Finsupp.single (.lit tag) (2 * N + 3 + q * (2 * N + 2) + 2 * q * (N + q + 2)) +
  Finsupp.single (.cmp tag) (q + 1) +
  Finsupp.single (.copy tag) (N + 2 * q * N)

/-- The exact target of the registered stored-matrix program: for every real ROM matrix and
input, the compiled tree succeeds within the stated counts and memory, and its output buffers
hold the input, every basis column, the coefficients $\alpha_j$, $\beta_j$, the input norm,
the final previous vector and the norms $\nu_{j+1}$ of `NLAlib.lanczosReorthState`. No symmetry,
nonzero-input or nonbreakdown premise is imposed. -/
def StoredEntriesLanczosReorth : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P),
    StoredEntries (𝕜 := ℝ) tag (lanczosReorthProg.compiled (ι := ι) tag)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N q b => ![(Array.ofFn b).map some, Array.replicate (N * (q 0 + 1)) none,
        Array.replicate (q 0) none, Array.replicate (q 0 + 1) none,
        Array.replicate 1 none, Array.replicate N none, Array.replicate (q 0) none])
      (fun N _ => N ^ 2) (fun N q => lanczosReorthCount tag N (q 0))
      (fun N q p => if p = tag then 2 * N ^ 2 + N * (q 0 + 5) + 5 * q 0 + 7 else 0)
      (fun N q b vals _ st =>
        let A : Matrix (Fin N) (Fin N) ℝ := fun i j => vals (i + N * j)
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
