/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosOracleExecution
public import NLAlib.Krylov.Processes.LanczosOracleStaticCost
public import NLAlib.Krylov.Processes.LanczosProgramInitialization
public import NLAlib.Krylov.Processes.LanczosProgramScope

/-!
# Exact realization of the oracle Lanczos target

The actual three allocations reserve an empty matrix slot and provide the work/scalar buffers.
Shared checked initialization and the actual oracle Paige loop give every requested recurrence
output. Scope cleanup retains the six declared buffers; static analysis supplies the resources.

## Main results

* `NLAlib.matrixFreeLanczos`: the full approved target, including input preservation and resources.
-/

@[expose] public section

namespace NLAlib.LanczosOracleImplementation

open Computation Computation.Builder LanczosImplementation

variable {P ι : Type} [DecidableEq P]

-- Local syntax abbreviates the actual approved subtrees in proof statements. It introduces
-- no second program definition or registered tree.
local macro "lanczosInit(" tag:term "," N:term "," scalars:term ")" : term => `(do
  ins (.lit $tag ⟨$scalars, 0⟩ 0)
  ins (.lit $tag ⟨3, 0⟩ 0)
  forRange (IExp.const ($N)) fun i => ins (.lit $tag ⟨5, IExp.var i⟩ 0)
  nrm2 $tag ⟨4, 0⟩ 0 0 (IExp.const ($N))
  ifThenElse $tag .eq ⟨4, 0⟩ ⟨$scalars, 0⟩
    (forRange (IExp.const ($N)) fun i => ins (.lit $tag ⟨1, IExp.var i⟩ 0)) (do
      copyv $tag 0 0 1 0 (IExp.const ($N))
      rscl $tag ⟨4, 0⟩ 1 0 (IExp.const ($N))))

local macro "lanczosOracleLoop(" tag:term "," N:term "," q:term ","
    o:term "," work:term "," scalars:term ")" : term =>
  `(forRange (IExp.const $q) fun j => do
    stmt (.apply $o $tag $work 0 1 (IExp.const ($N) * IExp.var j) 1)
    ins (.un $tag .neg ⟨$scalars, 1⟩ ⟨3, IExp.var j⟩)
    axpy $tag ⟨$scalars, 1⟩ 5 0 $work 0 (IExp.const ($N))
    dot $tag ⟨2, IExp.var j⟩ 1 (IExp.const ($N) * IExp.var j) $work 0 (IExp.const ($N))
    ins (.un $tag .neg ⟨$scalars, 1⟩ ⟨2, IExp.var j⟩)
    axpy $tag ⟨$scalars, 1⟩ 1 (IExp.const ($N) * IExp.var j) $work 0 (IExp.const ($N))
    nrm2 $tag ⟨3, IExp.var j + 1⟩ $work 0 (IExp.const ($N))
    copyv $tag 1 (IExp.const ($N) * IExp.var j) 5 0 (IExp.const ($N))
    ifThenElse $tag .eq ⟨3, IExp.var j + 1⟩ ⟨$scalars, 0⟩
      (forRange (IExp.const ($N)) fun i =>
        ins (.lit $tag ⟨1, IExp.const ($N) * (IExp.var j + 1) + IExp.var i⟩ 0)) (do
        copyv $tag $work 0 1 (IExp.const ($N) * (IExp.var j + 1)) (IExp.const ($N))
        rscl $tag ⟨3, IExp.var j + 1⟩ 1
          (IExp.const ($N) * (IExp.var j + 1)) (IExp.const ($N))))

private def workspaceState (tag : P) (N q : ℕ) (b : Fin N → ℝ) : St P ℝ (OpCount P ι) :=
  (((declaredState tag N q b).allocate tag 0 0).allocate tag N 0).allocate tag 2 0

private def cleanState (tag : P) (N : ℕ) (st : St P ℝ (OpCount P ι)) :
    St P ℝ (OpCount P ι) :=
  releaseWorkspace tag 0 N 0 st

private theorem workspace_shape (tag : P) (N q : ℕ) (b : Fin N → ℝ) :
    (workspaceState (ι := ι) tag N q b).store.shape = workspaceShape tag N q false := by
  simp [workspaceState, St.allocate, declaredState, inputState, workspaceShape, Store.shape]

private theorem workspace_input (tag : P) (N q : ℕ) (b : Fin N → ℝ) (i : Fin N) :
    (workspaceState (ι := ι) tag N q b).store.read tag 0 i = some (b i) := by
  simp [workspaceState, St.allocate, declaredState, inputState, Store.read, i.isLt]

private theorem exec_allocations (I : Interp P ι ℝ (OpCount P ι)) (tag : P)
    (hw : I.width tag = 0) (N q : ℕ) (b : Fin N → ℝ)
    (body : ℕ → ℕ → ℕ → Builder P ι ℕ ℕ Unit) (out : St P ℝ (OpCount P ι))
    (hbody : exec I (body 6 7 8).run (workspaceState tag N q b) = some out) :
    exec I (scope do
      let matrixSlot ← alloc tag 0
      let work ← alloc tag (.const N)
      let scalars ← alloc tag 2
      body matrixSlot work scalars).run (declaredState tag N q b) =
        some (cleanState tag N out) := by
  have hs : (declaredState (C := OpCount P ι) tag N q b).store.size = 6 := by
    simp [declaredState, inputState]
  have h := exec_scope_of_exec_eq_some I tag 0 N (declaredState tag N q b) out hs body
    (by simpa only [workspaceState, hw, IExp.eval_zero] using hbody)
  simpa only [cleanState, releaseWorkspace, hw, IExp.eval_zero] using h

private theorem exec_workspace (tag : P) (o : ι) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ) (b : Fin N → ℝ) :
    ∃ out, exec (exactInterp (fun _ => A) ξ) (do
      lanczosInit(tag,N,8)
      lanczosOracleLoop(tag,N,q,o,7,8)).run (workspaceState tag N q b) = some out ∧
      State tag N q q A b out false := by
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  obtain ⟨ini, eini, hctx, _, _, _, _, _, _⟩ := exec_initialize_of_workspace false I rfl
    (fun _ => rfl) tag N q (workspaceState tag N q b) A b (workspace_shape tag N q b)
      (workspace_input tag N q b) trivial
  obtain ⟨out, eloop, hout⟩ := exec_exact_loop tag o N q A ξ ini b hctx
  refine ⟨out, ?_, hout⟩
  rw [executionComposable_initialize I tag N, eini, Option.bind_some]
  exact eloop

private theorem declared_post (tag : P) {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {st : St P ℝ (OpCount P ι)} (h : State tag N q q A b st false) :
    let final := cleanState tag N st
    Holds final.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      Holds final.store tag 1 0 (lanczosMatrix A b (q + 1)) ∧
      Holds final.store tag 2 0
        (fun (j : Fin q) (_ : Fin 1) => lanczosAlpha A (lanczosState A b j)) ∧
      Holds final.store tag 3 0
        (fun (j : Fin (q + 1)) (_ : Fin 1) => (lanczosState A b j).beta) ∧
      final.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
      Holds final.store tag 5 0 (fun i (_ : Fin 1) => (lanczosState A b q).prev i) := by
  simpa only [cleanState, releaseWorkspace, St.release] using h.holds_pop_pop_pop

/-- The actual oracle tree runs for every real matrix and input. After freeing
all workspaces it retains b and computes every basis column and coefficient, the input norm
and final previous vector, including zero input/dimension/budget and zero continuation. -/
theorem exec_exact_program (tag : P) (o : ι) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ) (b : Fin N → ℝ) :
    ∃ final, exec (exactInterp (fun _ => A) ξ)
        (lanczosOracleProg tag o (.const N) (.const q) 0 1 2 3 4 5).run
        (inputState tag [(Array.ofFn b).map some, Array.replicate (N * (q + 1)) none,
          Array.replicate q none, Array.replicate (q + 1) none, Array.replicate 1 none,
          Array.replicate N none]) = some final ∧
      Holds final.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      Holds final.store tag 1 0 (lanczosMatrix A b (q + 1)) ∧
      Holds final.store tag 2 0
        (fun (j : Fin q) (_ : Fin 1) => lanczosAlpha A (lanczosState A b j)) ∧
      Holds final.store tag 3 0
        (fun (j : Fin (q + 1)) (_ : Fin 1) => (lanczosState A b j).beta) ∧
      final.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
      Holds final.store tag 5 0 (fun i (_ : Fin 1) => (lanczosState A b q).prev i) := by
  obtain ⟨out, erun, hstate⟩ := exec_workspace tag o N q A ξ b
  refine ⟨cleanState tag N out, ?_, declared_post tag hstate⟩
  exact exec_allocations (exactInterp (fun _ => A) ξ) tag rfl N q b
    (fun _ work scalars => do
      lanczosInit(tag,N,scalars)
      lanczosOracleLoop(tag,N,q,o,work,scalars)) out erun

end NLAlib.LanczosOracleImplementation

namespace NLAlib

open Computation

/-- **Matrix-free Lanczos recurrence.** For every real matrix $\mathbf A$, dimension $N$,
requested step count $q$ and input $\mathbf b$, the fixed tree
$\mathsf{lanczosOracleProg}(\mathbf A,\mathbf b,q)$ runs in exact arithmetic and preserves
its input. It returns all $q+1$ basis columns, $q$ alpha coefficients, $q+1$ beta coefficients,
the input norm and the final previous vector of the total $\mathsf{lanczosState}$ recurrence.
Zero dimension, zero input, zero budget and continuation after a zero next norm are included.
The Paige update order follows [Saad2003, Algorithm 6.15]; this algebraic implementation
correspondence holds for every real matrix.

Upper counts are $q$ oracle loads and one-column matvecs, $N+4qN$ multiplications and additions,
$N+2qN$ conjugations, $N(q+1)$ divisions, $q+1$ square roots, $2q$ negations,
$2N+3+q(N+2)$ literals, $q+1$ comparisons and $N+2qN$ copies. Peak numeric-cell memory,
including all declared outputs and scratch, is at most $N(q+4)+2q+5$ at the arithmetic tag
and zero elsewhere. The oracle backend's internal storage and arithmetic are outside this
access model. The guards and buffer layout are proved here.
Result: lanczos-oracle-program -/
theorem matrixFreeLanczos : MatrixFreeLanczos := by
  intro P ι inst tag o N n _ b A ξ
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  have hn : n = ![n 0] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  obtain ⟨out, erun, hpost⟩ :=
    LanczosOracleImplementation.exec_exact_program tag o N (n 0) A ξ b
  have ecompiled : (lanczosOracleProg.compiled tag o).exec I N ![n 0]
      (inputState tag [(Array.ofFn b).map some, Array.replicate (N * (n 0 + 1)) none,
        Array.replicate (n 0) none, Array.replicate (n 0 + 1) none, Array.replicate 1 none,
        Array.replicate N none]) = some out := by
    rw [Prog.exec_eq_exec_toStmt, lanczosOracleProg.toStmt_compiled]
    exact erun
  have hcost := lanczosOracleProg.bounds_of_exec_eq_some I tag o N (n 0) (fun _ => rfl) ecompiled
  refine ⟨by simp, out, ?_, ?_, ?_, hpost⟩
  · rw [hn]
    change (lanczosOracleProg.compiled tag o).exec I N ![n 0]
      (inputState tag [(Array.ofFn b).map some, Array.replicate (N * (n 0 + 1)) none,
        Array.replicate (n 0) none, Array.replicate (n 0 + 1) none, Array.replicate 1 none,
        Array.replicate N none]) = some out
    exact ecompiled
  · simpa only [inputState, zero_add] using hcost.count
  · intro p
    have hpeak := hcost.peak p
    change out.peak p + 0 ≤ if p = tag then N * (n 0 + 4) + 2 * n 0 + 5 else 0
    by_cases hp : p = tag
    · subst p
      simp [inputState, Nat.mul_add] at hpeak ⊢
      omega
    · simpa [inputState, hp] using hpeak

end NLAlib
