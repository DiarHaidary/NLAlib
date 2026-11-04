/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGOracleProgramTree
public import NLAlib.Krylov.LinearSystems.CGRecurrence

/-!
# Approved matrix-free CG target and resources

The fixed oracle tree is bound before every dimension, matrix and declared input. The target
requires unconditional exact execution and safe statuses, input preservation and SPD outputs.

## Main definitions

* `NLAlib.cgOracleCount`: the approved componentwise upper count.
* `NLAlib.MatrixFreeConjugateGradient`: the approved exact target.
-/

@[expose] public section

namespace NLAlib

open Computation
open scoped Matrix

/-- Componentwise upper counts for q requested iterations of the guarded oracle variant.
Oracle loads and one-column matvecs are charged separately; there are no matrix ROM reads. -/
noncomputable def cgOracleCount {P ι : Type} (tag : P) (o : ι) (N q : ℕ) : OpCount P ι :=
  Finsupp.single (.load tag o) q + Finsupp.single (.matvec tag o) q +
  Finsupp.single (.bin tag .mul) (N + 5 * q * N) +
  Finsupp.single (.bin tag .add) (N + 5 * q * N) +
  Finsupp.single (.un tag .conj) (N + 2 * q * N) +
  Finsupp.single (.bin tag .div) (2 * q) + Finsupp.single (.un tag .neg) (q + 1) +
  Finsupp.single (.lit tag) (N + 3 + 2 * q) +
  Finsupp.single (.cmp tag) (1 + 3 * q) + Finsupp.single (.copy tag) (2 * N + 2 * q + 2)

/-- The oracle target: all real inputs execute with legal status and preserved input;
for SPD A, x/r/p agree with the total exact recurrence, padded after zero termination.
The statement fixes the program before quantifying matrices, dimensions and input data. -/
def MatrixFreeConjugateGradient : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P) (o : ι),
    MatrixFree (𝕜 := ℝ) tag (cgOracleProg.compiled tag o)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N _ b => ![(Array.ofFn b).map some, Array.replicate N none,
        Array.replicate N none, Array.replicate N none, Array.replicate 1 none])
      (fun N q => cgOracleCount tag o N (q 0))
      (fun N _ p => if p = tag then 5 * N + 11 else 0)
      (fun _ q b A _ st =>
        ∃ status : ℝ, st.store.read tag 4 0 = some status ∧
          (status = 0 ∨ status = 1 ∨ status = -1) ∧
          Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
          (A.PosDef →
            Holds st.store tag 1 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).x i) ∧
            Holds st.store tag 2 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).r i) ∧
            Holds st.store tag 3 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).p i) ∧
            (status = 1 ↔ (cgState A b 0 (q 0)).r = 0) ∧ status ≠ -1))

end NLAlib
