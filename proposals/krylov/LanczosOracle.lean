/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.Model
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# Proposed matrix-free Lanczos implementation

One fixed oracle tree preserves the Paige update order and guarded zero continuation of the
stored implementation. It reserves an empty matrix slot to reuse the physical scalar and
vector layout. The oracle's internal storage and arithmetic are outside the access model.
Design: `docs/design/Lanczos-Matrix-Free-Program.md`.

## Main definitions

* `NLAlib.lanczosOracleProg`: the proposed oracle program.
* `NLAlib.lanczosOracleProg.compiled`: its fixed first-order tree.
* `NLAlib.lanczosOracleCount`: proposed operation counts.
* `NLAlib.MatrixFreeLanczos`: proposed target, awaiting approval and registration.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

/-- The proposed matrix-free Lanczos program. Declared buffers are the unchanged
input, all basis columns through the final state, alpha, beta, input norm and final previous
vector. Work storage is scoped; slot 6 is reserved empty. Initialization uses actual `nrm2`
and `rscl`, and
zero continuation performs every requested step without dividing by a zero norm.
The oracle's hidden storage and implementation arithmetic are outside this access model. -/
def lanczosOracleProg {P ι VB VI : Type} (tag : P) (o : ι) (N q : IExp VI)
    (b V alpha beta inputNorm prev : VB) : Builder P ι VB VI Unit := scope do
  let _matrixSlot ← alloc tag 0
  let work ← alloc tag N
  let scalars ← alloc tag 2
  ins (.lit tag ⟨scalars, 0⟩ 0)
  ins (.lit tag ⟨beta, 0⟩ 0)
  forRange N fun i => ins (.lit tag ⟨prev, .var i⟩ 0)
  nrm2 tag ⟨inputNorm, 0⟩ b 0 N
  ifThenElse tag .eq ⟨inputNorm, 0⟩ ⟨scalars, 0⟩
    (forRange N fun i => ins (.lit tag ⟨V, .var i⟩ 0)) (do
      copyv tag b 0 V 0 N
      rscl tag ⟨inputNorm, 0⟩ V 0 N)
  forRange q fun j => do
    stmt (.apply o tag work 0 V (N * .var j) 1)
    ins (.un tag .neg ⟨scalars, 1⟩ ⟨beta, .var j⟩)
    axpy tag ⟨scalars, 1⟩ prev 0 work 0 N
    dot tag ⟨alpha, .var j⟩ V (N * .var j) work 0 N
    ins (.un tag .neg ⟨scalars, 1⟩ ⟨alpha, .var j⟩)
    axpy tag ⟨scalars, 1⟩ V (N * .var j) work 0 N
    nrm2 tag ⟨beta, .var j + 1⟩ work 0 N
    copyv tag V (N * .var j) prev 0 N
    ifThenElse tag .eq ⟨beta, .var j + 1⟩ ⟨scalars, 0⟩
      (forRange N fun i => ins (.lit tag ⟨V, N * (.var j + 1) + .var i⟩ 0)) (do
        copyv tag work 0 V (N * (.var j + 1)) N
        rscl tag ⟨beta, .var j + 1⟩ V (N * (.var j + 1)) N)

/-- The proposed first-order tree, compiled once at symbolic dimension and step count.
It has six free buffers and uses one oracle call per Paige step. -/
def lanczosOracleProg.compiled {P ι : Type} (tag : P) (o : ι) : Prog P ι 1 6 :=
  (ProgFamily.compile fun _ _ N q h =>
    (lanczosOracleProg tag o N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)).run).get rfl

/-- The proposed tree instantiates to the concrete builder for every dimension and
requested step count. -/
theorem lanczosOracleProg.toStmt_compiled {P ι : Type} (tag : P) (o : ι) (N q : ℕ) :
    (lanczosOracleProg.compiled (ι := ι) tag o).toStmt N ![q] =
      (lanczosOracleProg tag o (.const N) (.const q) 0 1 2 3 4 5).run := rfl

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
