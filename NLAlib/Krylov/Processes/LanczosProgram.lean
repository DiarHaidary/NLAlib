/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramInitialization
public import NLAlib.Computation.ScalarFrames

/-!
# Exact realization of the approved stored Lanczos target

The declared input buffers are extended by the actual three scoped allocations. Matrix
entries come from the actual ROM loading loop; initialization and the Paige iteration loop
supply the exact recurrence outputs. Scope cleanup then preserves every declared output.

## Main results

* `NLAlib.storedEntriesLanczos`: the approved exact target of the registered tree.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Computation.Builder

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

local macro "lanczosLoop(" tag:term "," N:term "," q:term ","
    A:term "," work:term "," scalars:term ")" : term =>
  `(forRange (IExp.const $q) fun j => do
    gemv $tag (IExp.const ($N)) (IExp.const ($N)) $A 0 1 (IExp.const ($N) * IExp.var j) $work 0
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

local macro "lanczosBody(" tag:term "," N:term "," q:term ","
    A:term "," work:term "," scalars:term ")" : term => `(do
  forRange (IExp.const ($N) * IExp.const ($N)) fun i =>
    stmt (.rom $tag ⟨$A, IExp.var i⟩ (IExp.var i))
  lanczosInit($tag,$N,$scalars)
  lanczosLoop($tag,$N,$q,$A,$work,$scalars))

private def pushState (tag : P) (len : ℕ) (st : St P ℝ (OpCount P ι)) :
    St P ℝ (OpCount P ι) :=
  { st with store := st.store.push (tag, Array.replicate len none)
            cur := Function.update st.cur tag (st.cur tag + len)
            peak := Function.update st.peak tag (max (st.peak tag) (st.cur tag + len)) }

private def workspaceState (tag : P) (N q : ℕ) (b : Fin N → ℝ) :
    St P ℝ (OpCount P ι) :=
  pushState tag 2 (pushState tag N (pushState tag (N * N) (declaredState tag N q b)))

private theorem declared_shape (tag : P) (N q : ℕ) (b : Fin N → ℝ) :
    (declaredState (C := OpCount P ι) tag N q b).store.shape =
      #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)] := by
  simp [declaredState, inputState, Store.shape]

private theorem workspace_shape (tag : P) (N q : ℕ) (b : Fin N → ℝ) :
    (workspaceState (ι := ι) tag N q b).store.shape =
      #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N),
        (tag, N * N), (tag, N), (tag, 2)] := by
  simp [workspaceState, pushState, Store.shape, declaredState, inputState]

private theorem workspace_input (tag : P) (N q : ℕ) (b : Fin N → ℝ) :
    ∀ i : Fin N, (workspaceState (ι := ι) tag N q b).store.read tag 0 i = some (b i) := by
  intro i
  simp [workspaceState, pushState, declaredState, inputState, Store.read, i.isLt]

private theorem workspace_cur (tag : P) (N q : ℕ) (b : Fin N → ℝ) (p : P) :
    (workspaceState (ι := ι) tag N q b).cur p =
      if p = tag then N * N + N * (q + 4) + 2 * q + 4 else 0 := by
  by_cases hp : p = tag
  · subst p
    simp [workspaceState, pushState, declaredState, inputState]
    ring
  · simp [workspaceState, pushState, declaredState, inputState, hp]

private theorem workspace_peak (tag : P) (N q : ℕ) (b : Fin N → ℝ) :
    (workspaceState (ι := ι) tag N q b).peak = (workspaceState (ι := ι) tag N q b).cur := by
  funext p
  by_cases hp : p = tag
  · subst p
    simp [workspaceState, pushState, declaredState, inputState]
  · simp [workspaceState, pushState, declaredState, inputState, hp]

omit [DecidableEq P] in
private theorem compiled_toStmt (tag : P) (N : ℕ) (q : Fin 1 → ℕ) :
    (lanczosProg.compiled (ι := ι) tag).toStmt N q =
      (lanczosProg tag (.const N) (.const (q 0)) 0 1 2 3 4 5).run := rfl

private def popState (tag : P) (len : ℕ) (st : St P ℝ (OpCount P ι)) :
    St P ℝ (OpCount P ι) :=
  { st with store := st.store.pop
            cur := Function.update st.cur tag (st.cur tag - len) }

private def cleanState (tag : P) (N : ℕ) (st : St P ℝ (OpCount P ι)) :
    St P ℝ (OpCount P ι) :=
  popState tag (N * N) (popState tag N (popState tag 2 st))

private theorem exec_allocations (I : Interp P ι ℝ (OpCount P ι)) (tag : P)
    (hw : I.width tag = 0) (N q : ℕ) (b : Fin N → ℝ)
    (body : ℕ → ℕ → ℕ → Stmt P ι ℕ ℕ) :
    exec I (.alloc tag (IExp.const N * IExp.const N) fun A =>
        .alloc tag (.const N) fun work => .alloc tag 2 (body A work))
      (declaredState tag N q b) =
        (exec I (body 6 7 8) (workspaceState (ι := ι) tag N q b)).map (cleanState tag N) := by
  have hs : (declaredState (C := OpCount P ι) tag N q b).store.size = 6 := by
    simpa [Store.shape] using
      congrArg Array.size (declared_shape (ι := ι) tag N q b)
  simp only [exec_alloc, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat, hw,
    mul_zero, add_zero, Nat.sub_zero, hs, Array.size_push, Option.map_map]
  rfl

private theorem declared_post (tag : P) {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {st : St P ℝ (OpCount P ι)} (h : State tag N q q A b st) :
    Holds (cleanState tag N st).store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
    Holds (cleanState tag N st).store tag 1 0 (lanczosMatrix A b (q + 1)) ∧
    Holds (cleanState tag N st).store tag 2 0
      (fun (j : Fin q) (_ : Fin 1) => lanczosAlpha A (lanczosState A b j)) ∧
    Holds (cleanState tag N st).store tag 3 0
      (fun (j : Fin (q + 1)) (_ : Fin 1) => (lanczosState A b j).beta) ∧
    (cleanState tag N st).store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
    Holds (cleanState tag N st).store tag 5 0
      (fun i (_ : Fin 1) => (lanczosState A b q).prev i) := by
  simpa only [cleanState, popState] using h.holds_pop_pop_pop

private theorem memory_bound (tag : P) (N q : ℕ) (b : Fin N → ℝ)
    (vals : ℕ → ℝ) (ξ : Dist → ℕ → ℝ) (out : St P ℝ (OpCount P ι))
    (hp : out.peak ≤ Function.update (workspaceState (ι := ι) tag N q b).peak tag
      (max ((workspaceState (ι := ι) tag N q b).peak tag)
        ((workspaceState (ι := ι) tag N q b).cur tag + 1))) :
    ∀ p, (cleanState tag N out).peak p + (storedInterp (ι := ι) (N ^ 2) vals ξ tag).romSize p ≤
      if p = tag then 2 * N ^ 2 + N * (q + 4) + 2 * q + 5 else 0 := by
  intro p
  have h := hp p
  rw [workspace_peak] at h
  by_cases he : p = tag
  · subst p
    simp only [Function.update_self, workspace_cur, ite_true] at h
    simp only [cleanState, popState, storedInterp, ite_true]
    calc
      out.peak tag + N ^ 2 ≤
          max (N * N + N * (q + 4) + 2 * q + 4)
            (N * N + N * (q + 4) + 2 * q + 4 + 1) + N ^ 2 := Nat.add_le_add_right h _
      _ = 2 * N ^ 2 + N * (q + 4) + 2 * q + 5 := by
        rw [max_eq_right (Nat.le_succ _)]
        simp only [Nat.succ_eq_add_one]
        ring
  · simp only [Function.update_of_ne he, workspace_cur, if_neg he] at h
    simpa only [cleanState, popState, storedInterp, if_neg he, add_zero] using h

private theorem exec_load (tag : P) (N q : ℕ) (b : Fin N → ℝ)
    (vals : ℕ → ℝ) (ξ : Dist → ℕ → ℝ) :
    ∃ out, exec (storedInterp (ι := ι) (N ^ 2) vals ξ tag)
        (forRange (IExp.const N * IExp.const N) fun i =>
          stmt (.rom tag ⟨6, IExp.var i⟩ (IExp.var i))).run
        (workspaceState (ι := ι) tag N q b) = some out ∧
      out.store.shape = (workspaceState (ι := ι) tag N q b).store.shape ∧
      (∀ i : Fin N, out.store.read tag 0 i = some (b i)) ∧
      Holds out.store tag 6 0 (fun (i j : Fin N) => vals (i + N * j)) ∧
      out.pos = (workspaceState (ι := ι) tag N q b).pos ∧
      out.cur = (workspaceState (ι := ι) tag N q b).cur ∧
      out.curW = (workspaceState (ι := ι) tag N q b).curW ∧
      out.cnt = Finsupp.single (.rom tag) (N * N) ∧
      out.peak = (workspaceState (ι := ι) tag N q b).peak ∧
      out.peakW = (workspaceState (ι := ι) tag N q b).peakW := by
  let st := workspaceState (ι := ι) tag N q b
  let I := storedInterp (ι := ι) (N ^ 2) vals ξ tag
  have hs : st.store.shape[6]? = some (tag, (IExp.const N * IExp.const N : IExp ℕ).eval) := by
    rw [workspace_shape]; rfl
  obtain ⟨s', hr, hsh, hv, hf⟩ := Computation.exec_forRange_rom I tag st
    (IExp.const N * IExp.const N) 6 vals hs (by
      intro i hi
      exact if_pos (by simpa only [Nat.pow_two, IExp.eval_mul, IExp.eval_const] using hi))
  let out : St P ℝ (OpCount P ι) :=
    { st with store := s', cnt := st.cnt + (N * N) • I.charge (.rom tag) }
  refine ⟨out, ?_, hsh, ?_, ?_, rfl, rfl, rfl, ?_, rfl, rfl⟩
  · change exec I (.seq (.loop (IExp.const N * IExp.const N) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · intro i
    exact (hf tag 0 i (by decide)).trans (workspace_input tag N q b i)
  · intro i j
    simpa only [zero_add] using hv (i + N * j)
      (Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)
  · simp [out, st, I, storedInterp, workspaceState, pushState, declaredState, inputState,
      Finsupp.smul_single]

private theorem exec_scoped (tag : P) (N q : ℕ) (b : Fin N → ℝ)
    (vals : ℕ → ℝ) (ξ : Dist → ℕ → ℝ) (out : St P ℝ (OpCount P ι))
    (hr : exec (storedInterp (N ^ 2) vals ξ tag) (lanczosBody(tag,N,q,6,7,8)).run
      (workspaceState tag N q b) = some out) :
    exec (storedInterp (N ^ 2) vals ξ tag)
      (lanczosProg tag (.const N) (.const q) 0 1 2 3 4 5).run
      (declaredState tag N q b) = some (cleanState tag N out) := by
  have ht : (lanczosProg (ι := ι) (VB := ℕ) (VI := ℕ) tag (.const N) (.const q) 0 1 2 3 4 5).run =
      .seq (.alloc tag (IExp.const N * IExp.const N) fun A =>
        .alloc tag (.const N) fun work => .alloc tag 2 fun scalars =>
          (lanczosBody(tag,N,q,A,work,scalars)).run) .skip := rfl
  rw [ht, exec_seq_skip, exec_allocations _ tag rfl, hr, Option.map_some]

private theorem exec_body (tag : P) (N q : ℕ) (b : Fin N → ℝ)
    (vals : ℕ → ℝ) (ξ : Dist → ℕ → ℝ) :
    ∃ out, exec (storedInterp (N ^ 2) vals ξ tag) (lanczosBody(tag,N,q,6,7,8)).run
        (workspaceState (ι := ι) tag N q b) = some out ∧
      State tag N q q (fun i j => vals (i + N * j)) b out ∧
      out.cnt ≤ lanczosCount tag N q ∧
      out.peak ≤ Function.update (workspaceState (ι := ι) tag N q b).peak tag
        (max ((workspaceState (ι := ι) tag N q b).peak tag)
          ((workspaceState (ι := ι) tag N q b).cur tag + 1)) := by
  let I := storedInterp (ι := ι) (N ^ 2) vals ξ tag
  obtain ⟨loaded, hl, hsh, hb, hA, _, hcur, _, hcnt, hpeak, _⟩ :=
    exec_load (ι := ι) tag N q b vals ξ
  obtain ⟨start, hi, hs, _, hcuri, _, hcnti, hpeaki, _⟩ :=
    exec_initialize I rfl (fun _ => rfl) tag N q loaded
      (fun i j => vals (i + N * j)) b (hsh.trans (workspace_shape tag N q b)) hb hA
  obtain ⟨out, hr, hs', _, _, _, hcnt', hpeak', _⟩ := exec_steps I rfl (fun _ => rfl) tag start hs
  refine ⟨out, ?_, hs', ?_, ?_⟩
  · change exec I ((forRange (IExp.const N * IExp.const N) fun i =>
        stmt (.rom tag ⟨6, IExp.var i⟩ (IExp.var i))) >>= fun _ => do
          lanczosInit(tag,N,8)
          lanczosLoop(tag,N,q,6,7,8)).run (workspaceState tag N q b) = some out
    rw [exec_run_bind I (b := forRange (IExp.const N * IExp.const N) fun i =>
      stmt (.rom tag ⟨6, IExp.var i⟩ (IExp.var i))) (fun _ => rfl), hl, Option.bind_some]
    rw [executionComposable_initialize I tag N, hi, Option.bind_some]
    exact hr
  · calc
      out.cnt ≤ start.cnt + q • stepCount tag N := hcnt'
      _ ≤ (loaded.cnt + initializationCount tag N) + q • stepCount tag N :=
        add_le_add hcnti le_rfl
      _ = lanczosCount tag N q := by rw [hcnt, add_nsmul_eq_lanczosCount]
  · rw [hpeaki, hpeak, hcuri, hcur] at hpeak'
    simpa only [Function.update_self, max_assoc, max_self, Function.update_idem] using hpeak'

omit [DecidableEq P] in
/-- **Exact stored-entry Lanczos implementation.** For every dimension $N$, requested step
count $q$, real matrix $\mathbf{A}$ supplied column-major in ROM and real input $\mathbf{b}$,
the registered tree preserves the input and writes
$\mathsf{lanczosMatrix}(\mathbf{A},\mathbf{b},q+1)$, every diagonal coefficient through $q-1$,
every off-diagonal coefficient through $q$, the input norm, and the final previous vector.
These are the total Paige-order recurrence outputs, including zero dimension, zero input and
all steps after breakdown. No symmetry or other mathematical input restriction is imposed.
The recurrence is [Saad2003, Algorithm 6.15].

The counts are bounded componentwise by $N^2$ ROM reads, $N+q(N^2+4N)$ multiplications and
additions each, $N+2qN$ conjugations, $N(q+1)$ divisions, $q+1$ square roots, $2q$ negations,
$2N+3+q(2N+2)$ literals, $q+1$ comparisons, and $N+2qN$ copies. Peak memory, including ROM,
is at most $2N^2+N(q+4)+2q+5$ cells at the program tag and zero at every other tag.
The guarantee uses exact stored-entry semantics; it does not assume a rounding contract for a
machine carrier.
Result: lanczos-program -/
theorem _root_.NLAlib.storedEntriesLanczos : StoredEntriesLanczos := by
  intro P ι inst tag N q _ b vals ξ
  rw [Prog.runsWithin_iff (hsize := by simp), compiled_toStmt]
  change RunsWithin (storedInterp (N ^ 2) vals ξ tag)
    (lanczosProg tag (.const N) (.const (q 0)) 0 1 2 3 4 5).run
    (declaredState tag N (q 0) b) (lanczosCount tag N (q 0)) _ _
  obtain ⟨out, hr, hs, hcnt, hpeak⟩ := exec_body (ι := ι) tag N (q 0) b vals ξ
  refine ⟨cleanState tag N out, exec_scoped tag N (q 0) b vals ξ out hr, ?_,
    memory_bound tag N (q 0) b vals ξ out hpeak, ?_⟩
  · simpa only [cleanState, popState, declaredState, inputState, zero_add] using hcnt
  · exact declared_post tag hs

/-- **The Lanczos target is not vacuous**
(`docs/design/Computation-Hardening.md`, §2.2): for every $N_0$ there are tags and oracle names
(`Unit`) and sizes $N = N_0 + 1$, $n = (1)$ (no size condition), the declared input type
$\mathbb{R}^N$ inhabited (by the zero vector). The witness of `NLAlib.StoredEntriesLanczos`
(`scripts/Targets.lean`, item 7). No printed source. -/
theorem _root_.NLAlib.storedEntriesLanczos_nonVacuous : ∀ N₀ : ℕ,
    ∃ (P ι : Type) (_ : DecidableEq P) (tag : P),
    StoredEntries.NonVacuous (𝕜 := ℝ) tag (lanczosProg.compiled (ι := ι) tag)
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
        Holds st.store tag 5 0 (fun i (_ : Fin 1) => (lanczosState A b (q 0)).prev i)) N₀ :=
  fun N₀ => ⟨Unit, Unit, inferInstance, (), N₀ + 1, fun _ => 1, Nat.le_succ N₀, trivial,
    ⟨0⟩⟩

end NLAlib.LanczosImplementation
