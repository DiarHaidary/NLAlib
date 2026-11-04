/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosOracleProgramTree
public import NLAlib.Krylov.Processes.LanczosProgramStep
public import NLAlib.Krylov.Processes.LanczosProgramInitialization

/-!
# Exact execution of the oracle Lanczos steps

The actual offset oracle application is followed by the existing checked scalar, norm and
copy phases. The shared empty-matrix-slot invariant retains the input and all computed
prefixes. No symmetry, positive-definiteness or nonbreakdown premise is imposed.

## Main results

* `NLAlib.LanczosOracleImplementation.exec_exact_step`: actual oracle Paige step.
* `NLAlib.LanczosOracleImplementation.exec_exact_loop`: actual full oracle loop.
-/

@[expose] public section

namespace NLAlib.LanczosOracleImplementation

open Computation Computation.Builder LanczosImplementation
open scoped Matrix

variable {P ι : Type} [DecidableEq P]

local macro "oracleMvPrev(" tag:term "," o:term "," N:term "," j:term ")" : term => `(do
  stmt (.apply $o $tag 7 0 1 (IExp.const ($N) * IExp.var ($j)) 1)
  ins (.un $tag .neg ⟨8, 1⟩ ⟨3, IExp.var ($j)⟩)
  axpy $tag ⟨8, 1⟩ 5 0 7 0 (IExp.const ($N)))

private theorem exec_oracle_matvec (tag : P) (o : ι) {N q j : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ} (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (h : State tag N q j A b st false) :
    ∃ mid, exec (exactInterp (fun _ => A) ξ)
        (stmt (.apply o tag 7 0 1 (.const N * .var j) 1)).run st = some mid ∧
      State tag N q j A b mid false ∧
      ∀ i : Fin N, mid.store.read tag 7 i = some ((A *ᵥ (lanczosState A b j).cur) i) := by
  let W : Matrix (Fin N) (Fin 1) ℝ := fun i _ => (lanczosState A b j).cur i
  have hsrc : ∀ (a : Fin N) (c : Fin 1),
      st.store.read tag 1 ((IExp.const N * .var j).eval + (N * c + a)) = some (W a c) := by
    intro a c
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_var, Fin.val_zero,
      mul_zero, zero_add, W] using h.basis j le_rfl a
  obtain ⟨store, hw⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (s := st.store) (p := tag) (b := 7) (off := 0) (xs := flatten (A * W)) (by
      intro i hi
      exact ⟨N, by rw [h.shape]; rfl, by simpa only [size_flatten, Nat.mul_one, zero_add] using hi⟩)
  let mid : St P ℝ (OpCount P ι) :=
    { st with
      store := store
      cnt := st.cnt + (Finsupp.single (.load tag o) 1 +
        1 • Finsupp.single (.matvec tag o) 1) }
  have he : exec (exactInterp (fun _ => A) ξ)
      (stmt (.apply o tag 7 0 1 (.const N * .var j) 1)).run st = some mid := by
    change exec _ (.seq (.apply o tag 7 0 1 (.const N * .var j) 1) .skip) st = _
    rw [exec_seq_skip]
    exact exec_apply_exactInterp_offset (m := 1) A ξ o tag 7 1 (0 : IExp ℕ)
      (IExp.const N * IExp.var j) (1 : IExp ℕ) rfl st W
      (by decide) hsrc hw
  have hframe (p : P) (k i : ℕ) (hk : k ≠ 7) :
      mid.store.read p k i = st.store.read p k i :=
    Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hk)
  have hs : State tag N q j A b mid false :=
    h.of_frame (Store.shape_of_writeBlock_eq_some hw) (fun p k i hk _ _ _ => hframe p k i hk)
  refine ⟨mid, he, hs, fun i => ?_⟩
  have hr := Store.read_of_writeBlock_eq_some_of_lt hw
    (by simpa only [size_flatten, Nat.mul_one] using i.isLt)
  have hf := getElem?_flatten (A * W) i (0 : Fin 1)
  have hm : (A * W) i 0 = (A *ᵥ (lanczosState A b j).cur) i := rfl
  exact (show mid.store.read tag 7 i = _ from by simpa only [zero_add] using hr).trans
    (by simpa only [Fin.val_zero, mul_zero, add_zero, hm] using hf)

private theorem exec_oracle_mv_prev (tag : P) (o : ι) {N q j : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ} (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (h : State tag N q j A b st false) :
    ∃ out, exec (exactInterp (fun _ => A) ξ) oracleMvPrev(tag,o,N,j).run st = some out ∧
      State tag N q j A b out false ∧
      ∀ i : Fin N, out.store.read tag 7 i =
        some ((A *ᵥ (lanczosState A b j).cur -
          (lanczosState A b j).beta • (lanczosState A b j).prev) i) := by
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  let s := lanczosState A b j
  obtain ⟨mid, hg, hs, hr⟩ := exec_oracle_matvec tag o ξ st h
  obtain ⟨tmp, htmp⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) (0 : ℝ)
    (show mid.store.shape[8]? = some (tag, 2) by rw [hs.shape]; rfl) (by decide)
  obtain ⟨out, hn, hsn, hrn, hfn, _, _, _, _, _, _⟩ :=
    exec_neg_axpy_count I rfl (fun _ => rfl) tag mid N ![5, 7, 3, 8] (by decide)
      0 0 (.var j) 1 s.beta s.prev (A *ᵥ s.cur) (hs.beta j le_rfl)
      (fun i => by simpa only [IExp.eval_zero, zero_add, Matrix.cons_val_zero] using hs.prev i)
      (fun i => by
        simpa only [IExp.eval_zero, zero_add, Matrix.cons_val_one, Matrix.cons_val_zero]
          using hr i) ⟨0, tmp, htmp⟩
  have hstate : State tag N q j A b out false := hs.of_frame hsn (by
    intro p k i hk _ _ ht
    exact hfn p k i (Or.inl hk) ht)
  refine ⟨out, ?_, hstate, fun i => ?_⟩
  · rw [exec_run_bind I (b := stmt (.apply o tag 7 0 1 (.const N * .var j) 1))
      (fun _ => rfl), hg, Option.bind_some]
    exact hn
  · simpa only [s, Matrix.cons_val_zero, Matrix.cons_val_one, IExp.eval_zero, zero_add,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hrn i

local macro "oracleProject(" tag:term "," N:term "," j:term ")" : term => `(do
  dot $tag ⟨2, IExp.var ($j)⟩ 1 (IExp.const ($N) * IExp.var ($j)) 7 0 (IExp.const ($N))
  ins (.un $tag .neg ⟨8, 1⟩ ⟨2, IExp.var ($j)⟩)
  axpy $tag ⟨8, 1⟩ 1 (IExp.const ($N) * IExp.var ($j)) 7 0 (IExp.const ($N)))

local macro "oracleCommit(" tag:term "," N:term "," j:term ")" : term => `(do
  copyv $tag 1 (IExp.const ($N) * IExp.var ($j)) 5 0 (IExp.const ($N))
  ifThenElse $tag .eq ⟨3, IExp.var ($j) + 1⟩ ⟨8, 0⟩
    (forRange (IExp.const ($N)) fun i =>
      ins (.lit $tag ⟨1, IExp.const ($N) * (IExp.var ($j) + 1) + IExp.var i⟩ 0)) (do
      copyv $tag 7 0 1 (IExp.const ($N) * (IExp.var ($j) + 1)) (IExp.const ($N))
      rscl $tag ⟨3, IExp.var ($j) + 1⟩ 1
        (IExp.const ($N) * (IExp.var ($j) + 1)) (IExp.const ($N))))

local macro "oracleStep(" tag:term "," o:term "," N:term "," j:term ")" : term => `(do
  stmt (.apply $o $tag 7 0 1 (IExp.const ($N) * IExp.var ($j)) 1)
  ins (.un $tag .neg ⟨8, 1⟩ ⟨3, IExp.var ($j)⟩)
  axpy $tag ⟨8, 1⟩ 5 0 7 0 (IExp.const ($N))
  dot $tag ⟨2, IExp.var ($j)⟩ 1 (IExp.const ($N) * IExp.var ($j)) 7 0 (IExp.const ($N))
  ins (.un $tag .neg ⟨8, 1⟩ ⟨2, IExp.var ($j)⟩)
  axpy $tag ⟨8, 1⟩ 1 (IExp.const ($N) * IExp.var ($j)) 7 0 (IExp.const ($N))
  nrm2 $tag ⟨3, IExp.var ($j) + 1⟩ 7 0 (IExp.const ($N))
  copyv $tag 1 (IExp.const ($N) * IExp.var ($j)) 5 0 (IExp.const ($N))
  ifThenElse $tag .eq ⟨3, IExp.var ($j) + 1⟩ ⟨8, 0⟩
    (forRange (IExp.const ($N)) fun i =>
      ins (.lit $tag ⟨1, IExp.const ($N) * (IExp.var ($j) + 1) + IExp.var i⟩ 0)) (do
      copyv $tag 7 0 1 (IExp.const ($N) * (IExp.var ($j) + 1)) (IExp.const ($N))
      rscl $tag ⟨3, IExp.var ($j) + 1⟩ 1
        (IExp.const ($N) * (IExp.var ($j) + 1)) (IExp.const ($N))))

private theorem executionComposable_mv_prev {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (o : ι) (N j : ℕ) :
    ExecutionComposable I (oracleMvPrev(tag,o,N,j) : Builder P ι ℕ ℕ Unit) := by
  exact
    ExecutionComposable.bind (I := I)
      (a := stmt (.apply o tag 7 0 1 (IExp.const N * IExp.var j) 1))
      (b := do
        ins (.un tag .neg ⟨8, 1⟩ ⟨3, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 5 0 7 0 (IExp.const N))
      (executionComposable_single I
        (b := stmt (.apply o tag 7 0 1 (IExp.const N * IExp.var j) 1)) (fun _ => rfl))
      (ExecutionComposable.bind (I := I)
        (a := ins (.un tag .neg ⟨8, 1⟩ ⟨3, IExp.var j⟩))
        (b := axpy tag ⟨8, 1⟩ 5 0 7 0 (IExp.const N))
        (executionComposable_single I (b := ins (.un tag .neg ⟨8, 1⟩ ⟨3, IExp.var j⟩))
          (fun _ => rfl))
        (executionComposable_single I (b := axpy tag ⟨8, 1⟩ 5 0 7 0 (IExp.const N))
          (fun _ => rfl)))

private theorem executionComposable_project {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (N j : ℕ) :
    ExecutionComposable I (oracleProject(tag,N,j) : Builder P ι ℕ ℕ Unit) := by
  exact
    ExecutionComposable.bind (I := I)
      (a := dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N))
      (b := do
        ins (.un tag .neg ⟨8, 1⟩ ⟨2, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N))
      (executionComposable_single I
        (b := dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N))
        (fun _ => rfl))
      (ExecutionComposable.bind (I := I)
        (a := ins (.un tag .neg ⟨8, 1⟩ ⟨2, IExp.var j⟩))
        (b := axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N))
        (executionComposable_single I (b := ins (.un tag .neg ⟨8, 1⟩ ⟨2, IExp.var j⟩))
          (fun _ => rfl))
        (executionComposable_single I
          (b := axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)) (fun _ => rfl)))

/-- One actual oracle Paige step advances the exact recurrence prefix, reusing the checked
projection, next-norm and guarded commit phases. The oracle acts on the current basis column
at its actual offset; terminal zero continuation and zero dimension need no extra premise. -/
theorem exec_exact_step (tag : P) (o : ι) (N q j : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ) (h : State tag N q j A b st false)
    (hj : j < q) :
    ∃ out, exec (exactInterp (fun _ => A) ξ)
        (oracleStep(tag,o,N,j) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      State tag N q (j + 1) A b out false := by
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  obtain ⟨s₁, hr₁, hs₁, hw₁⟩ := exec_oracle_mv_prev tag o ξ st h
  obtain ⟨s₂, hr₂, hs₂, ha₂, hw₂, _, _, _, _, _, _⟩ :=
    exec_project (storedMatrix := false) I rfl (fun _ => rfl) tag s₁ hs₁ hj hw₁
  obtain ⟨s₃, hr₃, hs₃, ha₃, hb₃, hw₃, _, _, _, _, _, _⟩ :=
    exec_next_norm (storedMatrix := false) I rfl (fun _ => rfl) tag s₂ hs₂ hj ha₂ hw₂
  obtain ⟨out, hr₄, hs₄, _, _, _, _, _, _⟩ :=
    exec_commit (storedMatrix := false) I rfl (fun _ => rfl) tag s₃ hs₃ hj ha₃ hb₃ hw₃
  have cMv := executionComposable_mv_prev I tag o N j
  have cProj := executionComposable_project I tag N j
  refine ⟨out, ?_, hs₄⟩
  change exec I (do
    oracleMvPrev(tag,o,N,j)
    oracleProject(tag,N,j)
    nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (.const N)
    oracleCommit(tag,N,j)).run st = some out
  rw [cMv, hr₁, Option.bind_some, cProj, hr₂, Option.bind_some,
    exec_run_bind I (b := nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (.const N)) (fun _ => rfl),
    hr₃, Option.bind_some]
  exact hr₄

/-- The actual oracle loop computes the full exact recurrence prefix for every real matrix,
input and natural horizon. It preserves the input and includes terminal zero continuation.
Resource bounds come independently from the static analysis of the approved fixed tree. -/
theorem exec_exact_loop (tag : P) (o : ι) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ) (h : State tag N q 0 A b st false) :
    ∃ out, exec (exactInterp (fun _ => A) ξ)
        (forRange (.const q) fun j =>
          (oracleStep(tag,o,N,j) : Builder P ι ℕ ℕ Unit)).run st = some out ∧
      State tag N q q A b out false := by
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  obtain ⟨out, hr, hs⟩ := exists_exec_loop_eq_some_of_forall I
    (n := .const q) (body := fun j => (oracleStep(tag,o,N,j) : Builder P ι ℕ ℕ Unit).run)
    (fun j mid => State tag N q j A b mid false) h
    (fun j hj mid hm => exec_exact_step tag o N q j A ξ mid b hm hj)
  refine ⟨out, ?_, hs⟩
  change exec I (.seq (.loop (.const q)
    (fun j => (oracleStep(tag,o,N,j) : Builder P ι ℕ ℕ Unit).run)) .skip) st = _
  rw [exec_seq_skip]
  exact hr

end NLAlib.LanczosOracleImplementation
