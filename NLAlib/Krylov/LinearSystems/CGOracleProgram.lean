/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGOracleProgramInitialization
public import NLAlib.Krylov.LinearSystems.CGOracleProgramLoop
public import NLAlib.Krylov.LinearSystems.CGProgramScope
public import NLAlib.Krylov.LinearSystems.CGOracleProgramStaticCost

/-!
# Whole exact execution of the oracle CG program

The checked initializer and loop run inside the actual three allocations. Their scope cleanup
preserves every declared output and the input. Resource bounds are supplied separately by
static analysis of the same fixed compiled tree.

## Main results

* `NLAlib.CGOracleImplementation.exec_exact_program`: actual guarded oracle program correctness.
* `NLAlib.matrixFreeConjugateGradient`: the approved target, including outputs and resources.
-/

@[expose] public section

namespace NLAlib.CGOracleImplementation

open Computation Computation.Builder CGImplementation
open scoped Matrix

variable {P ι : Type} [DecidableEq P]

private def workspaceState (tag : P) (N : ℕ) (b : Fin N → ℝ) : St P ℝ (OpCount P ι) :=
  (((declaredState tag N b).allocate tag 0 0).allocate tag N 0).allocate tag 9 0

private def releasedState (tag : P) (N : ℕ) (out : St P ℝ (OpCount P ι)) :
    St P ℝ (OpCount P ι) :=
  releaseWorkspace tag 0 N 0 out

private theorem workspace_shape (tag : P) (N : ℕ) (b : Fin N → ℝ) :
    (workspaceState (ι := ι) tag N b).store.shape = workspaceShape tag N false := by
  simp [workspaceState, declaredState, St.allocate, inputState, workspaceShape, Store.shape]

private theorem workspace_input (tag : P) (N : ℕ) (b : Fin N → ℝ) (i : Fin N) :
    (workspaceState (ι := ι) tag N b).store.read tag 0 i = some (b i) := by
  simp [workspaceState, declaredState, St.allocate, inputState, Store.read, i.isLt]

private theorem exec_allocations (I : Interp P ι ℝ (OpCount P ι)) (tag : P)
    (N : ℕ) (b : Fin N → ℝ) (hw : I.width tag = 0)
    (body : ℕ → ℕ → ℕ → Builder P ι ℕ ℕ Unit) (out : St P ℝ (OpCount P ι))
    (hbody : exec I (body 5 6 7).run (workspaceState tag N b) = some out) :
    exec I (scope do
      let matrixSlot ← alloc tag 0
      let s ← alloc tag (.const N)
      let scalars ← alloc tag 9
      body matrixSlot s scalars).run (declaredState tag N b) =
        some (releasedState tag N out) := by
  have hsize : (declaredState (C := OpCount P ι) tag N b).store.size = 5 := by
    simp [declaredState, inputState]
  have h := exec_scope_of_exec_eq_some I tag 0 N (declaredState tag N b) out hsize body
    (by simpa only [hw, IExp.eval_zero, workspaceState] using hbody)
  simpa only [hw, IExp.eval_zero, releasedState] using h

private theorem exec_workspace (tag : P) (o : ι) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ) (b : Fin N → ℝ) :
    ∃ out, exec (exactInterp (fun _ => A) ξ) (do
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)
      dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())
      forRange (.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
        (do
          stmt (.apply o tag 6 0 3 0 1)
          dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
          ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
            ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
            axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
            ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
            axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
            dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
            ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
            forRange (.const N) fun i => do
              ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
              ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
            ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
            ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
              (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
            (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) (pure ())).run (workspaceState tag N b) = some out ∧
      LoopInvariant tag N A b q out.store false := by
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  obtain ⟨ini, eini, hctx, _, _, _⟩ := exec_initialize I rfl (fun _ => rfl) tag N A b
    (workspaceState tag N b) (workspace_shape tag N b) (workspace_input tag N b)
  obtain ⟨out, eloop, hinv, _, _, _⟩ := exec_exact_loop tag o N q A ξ ini b hctx
  refine ⟨out, ?_, hinv⟩
  change exec I ((do
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)
      dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())
) >>= fun _ =>
      forRange (.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
        (do
          stmt (.apply o tag 6 0 3 0 1)
          dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
          ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
            ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
            axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
            ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
            axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
            dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
            ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
            forRange (.const N) fun i => do
              ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
              ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
            ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
            ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
              (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
            (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) (pure ())).run (workspaceState tag N b) = some out
  rw [executionComposable_initialize I tag N, eini, Option.bind_some]
  exact eloop

private theorem post_released (tag : P) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (out : St P ℝ (OpCount P ι))
    (hinv : LoopInvariant tag N A b q out.store false) :
    let final := releasedState tag N out
    ∃ status : ℝ, final.store.read tag 4 0 = some status ∧
      (status = 0 ∨ status = 1 ∨ status = -1) ∧
      Holds final.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      (A.PosDef →
        Holds final.store tag 1 0 (fun i (_ : Fin 1) => (cgState A b 0 q).x i) ∧
        Holds final.store tag 2 0 (fun i (_ : Fin 1) => (cgState A b 0 q).r i) ∧
        Holds final.store tag 3 0 (fun i (_ : Fin 1) => (cgState A b 0 q).p i) ∧
        (status = 1 ↔ (cgState A b 0 q).r = 0) ∧ status ≠ -1) := by
  obtain ⟨v, status, ctx, allowed, _, exactv⟩ := hinv
  have hsize : out.store.size = 8 := by rw [← Store.size_shape, ctx.shape]; rfl
  have popread (p : P) (buf i : ℕ) (hbuf : buf < 5) :
      (releasedState tag N out).store.read p buf i = out.store.read p buf i :=
    read_releaseWorkspace tag 0 N 0 out hsize p buf i hbuf
  have holds (buf : ℕ) (hbuf : buf < 5) (x : Fin N → ℝ)
      (hx : ∀ i : Fin N, ∃ w, out.store.read tag buf i = some w ∧ w = x i) :
      Holds (releasedState tag N out).store tag buf 0 (fun i (_ : Fin 1) => x i) := by
    intro i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [Fin.val_zero, mul_zero, add_zero, zero_add]
    rw [popread tag buf i hbuf]
    obtain ⟨w, hw, hval⟩ := hx i
    simpa only [hval] using hw
  refine ⟨status, ?_, allowed, holds 0 (by omega) b ctx.input, ?_⟩
  · rw [popread tag 4 0 (by omega)]
    obtain ⟨w, hw, hval⟩ := ctx.statusValue
    simpa only [hval] using hw
  · intro hA
    obtain ⟨hv, hterm, hneg⟩ := exactv hA
    subst v
    exact ⟨holds 1 (by omega) _ ctx.iterate, holds 2 (by omega) _ ctx.residual,
      holds 3 (by omega) _ ctx.direction, hterm, hneg⟩

/-- The actual oracle program executes for every real matrix and input, preserves
its input and returns a legal status. For SPD matrices all three physical vector buffers
agree with the total exact recurrence, including zero and terminal continuation cases. -/
theorem exec_exact_program (tag : P) (o : ι) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ) (b : Fin N → ℝ) :
    ∃ final, exec (exactInterp (fun _ => A) ξ)
        (cgOracleProg tag o (.const N) (.const q) 0 1 2 3 4).run
        (inputState tag [(Array.ofFn b).map some, Array.replicate N none,
          Array.replicate N none, Array.replicate N none, Array.replicate 1 none]) = some final ∧
      ∃ status : ℝ, final.store.read tag 4 0 = some status ∧
      (status = 0 ∨ status = 1 ∨ status = -1) ∧
      Holds final.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      (A.PosDef →
        Holds final.store tag 1 0 (fun i (_ : Fin 1) => (cgState A b 0 q).x i) ∧
        Holds final.store tag 2 0 (fun i (_ : Fin 1) => (cgState A b 0 q).r i) ∧
        Holds final.store tag 3 0 (fun i (_ : Fin 1) => (cgState A b 0 q).p i) ∧
        (status = 1 ↔ (cgState A b 0 q).r = 0) ∧ status ≠ -1) := by
  obtain ⟨out, erun, hinv⟩ := exec_workspace tag o N q A ξ b
  refine ⟨releasedState tag N out, ?_, post_released tag N q A b out hinv⟩
  exact exec_allocations (exactInterp (fun _ => A) ξ) tag N b rfl
    (fun _ s scalars => do
      ins (.lit tag ⟨scalars, 6⟩ 0)
      ins (.lit tag ⟨scalars, 7⟩ 1)
      ins (.un tag .neg ⟨scalars, 8⟩ ⟨scalars, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨scalars, 6⟩)
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)
      dot tag ⟨scalars, 0⟩ 2 0 2 0 (.const N)
      ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 7⟩)) (pure ())
      forRange (.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨scalars, 6⟩
        (do
          stmt (.apply o tag s 0 3 0 1)
          dot tag ⟨scalars, 2⟩ 3 0 s 0 (.const N)
          ifThenElse tag .lt ⟨scalars, 6⟩ ⟨scalars, 2⟩ (do
            ins (.bin tag .div ⟨scalars, 3⟩ ⟨scalars, 0⟩ ⟨scalars, 2⟩)
            axpy tag ⟨scalars, 3⟩ 3 0 1 0 (.const N)
            ins (.un tag .neg ⟨scalars, 5⟩ ⟨scalars, 3⟩)
            axpy tag ⟨scalars, 5⟩ s 0 2 0 (.const N)
            dot tag ⟨scalars, 1⟩ 2 0 2 0 (.const N)
            ins (.bin tag .div ⟨scalars, 4⟩ ⟨scalars, 1⟩ ⟨scalars, 0⟩)
            forRange (.const N) fun i => do
              ins (.bin tag .mul ⟨scalars, 2⟩ ⟨scalars, 4⟩ ⟨3, .var i⟩)
              ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨scalars, 2⟩)
            ins (.copy tag ⟨scalars, 0⟩ ⟨scalars, 1⟩)
            ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
              (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 7⟩)) (pure ()))
            (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 8⟩))) (pure ())) out erun

end NLAlib.CGOracleImplementation

namespace NLAlib

open Computation

/-- **Matrix-free conjugate gradients.** For every real matrix $\mathbf A$, dimension $N$
and requested budget $q$, including zero, the fixed tree $\mathsf{cgOracleProg}(\mathbf A,
\mathbf b,q)$ runs in exact arithmetic from zero, preserves its input and returns a legal
status. Zero residual stops active steps, and nonpositive curvature is rejected before division.
For positive-definite $\mathbf A$, all three output vectors equal $\mathsf{cgState}$ after
$q$ steps with zero continuation; status $1$ is equivalent to terminal zero residual and
negative status is excluded. [HestenesStiefel1952, (3:1)]; the fixed oracle program, guards
and buffer layout are proved here.

Upper counts are $q$ oracle loads and one-column matvecs, $N+5qN$ multiplications and additions,
$N+2qN$ conjugations, $2q$ divisions, $q+1$ negations, $N+3+2q$ literals, $1+3q$ comparisons
and $2N+2q+2$ copies. Peak numeric-cell memory, including all declared buffers and scratch,
is at most $5N+11$ at the arithmetic tag and zero elsewhere. The oracle backend's internal
storage and arithmetic are outside this access model.
Result: cg-oracle-program -/
theorem matrixFreeConjugateGradient : MatrixFreeConjugateGradient := by
  intro P ι inst tag o N n _ b A ξ
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  have hn : n = ![n 0] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  obtain ⟨out, erun, hpost⟩ := CGOracleImplementation.exec_exact_program tag o N (n 0) A ξ b
  have ecompiled : (cgOracleProg.compiled tag o).exec I N ![n 0]
      (inputState tag [(Array.ofFn b).map some, Array.replicate N none,
        Array.replicate N none, Array.replicate N none, Array.replicate 1 none]) = some out := by
    rw [Prog.exec_eq_exec_toStmt, cgOracleProg.toStmt_compiled]
    exact erun
  have hcost := cgOracleProg.bounds_of_exec_eq_some I tag o N (n 0) (fun _ => rfl) ecompiled
  refine ⟨by simp, out, ?_, ?_, ?_, hpost⟩
  · rw [hn]
    change (cgOracleProg.compiled tag o).exec I N ![n 0]
      (inputState tag [(Array.ofFn b).map some, Array.replicate N none,
        Array.replicate N none, Array.replicate N none, Array.replicate 1 none]) = some out
    exact ecompiled
  · simpa only [inputState, zero_add] using hcost.count
  · intro p
    have hpeak := hcost.peak p
    change out.peak p + 0 ≤ if p = tag then 5 * N + 11 else 0
    by_cases hp : p = tag
    · subst p
      simp [inputState] at hpeak ⊢
      omega
    · simpa [inputState, hp] using hpeak

/-- **The matrix-free conjugate-gradient target is not vacuous**
(`docs/design/Computation-Hardening.md`, §2.2): for every $N_0$ there are tags and oracle names
(`Unit`) and sizes $N = N_0 + 1$, $n = (1)$ (no size condition), the declared input type
$\mathbb{R}^N$ inhabited (by the zero vector). The witness of `NLAlib.MatrixFreeConjugateGradient`
(`scripts/Targets.lean`, item 7). No printed source. -/
theorem matrixFreeConjugateGradient_nonVacuous : ∀ N₀ : ℕ,
    ∃ (P ι : Type) (_ : DecidableEq P) (tag : P) (o : ι),
    MatrixFree.NonVacuous (𝕜 := ℝ) tag (cgOracleProg.compiled tag o)
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
            (status = 1 ↔ (cgState A b 0 (q 0)).r = 0) ∧ status ≠ -1)) N₀ :=
  fun N₀ => ⟨Unit, Unit, inferInstance, (), (), N₀ + 1, fun _ => 1, Nat.le_succ N₀, trivial,
    ⟨0⟩⟩

end NLAlib
