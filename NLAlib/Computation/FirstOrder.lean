/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Compile
public import NLAlib.Computation.RunsWithin

/-!
# The run of a first-order program

The run `NLAlib.Computation.FStmt.exec I s ρB ρI st` of a first-order statement takes an
environment of handles `ρB` and of index values `ρI`. Its leaves are the clauses of
`NLAlib.Computation.exec`, with each index expression evaluated in the environment; `alloc` binds
the new handle `st.store.size` and `loop` the iteration index. Every charge, memory and failure
rule is that of `exec`, clause for clause. The leaves are written out rather than delegated to
`exec`, so that a statement about a first-order program does not unfold to the builder's syntax;
the copies cannot drift apart from `exec`, because the bridge below is a theorem.

`NLAlib.Computation.Prog.exec prog N n` runs a program at the sizes $N$ and $n$, declared buffer
$j$ at handle $j$, and `NLAlib.Computation.Prog.RunsWithin` is its run within a budget, the
first-order form of `NLAlib.Computation.RunsWithin`.

**The bridge** (`NLAlib.Computation.FStmt.exec_eq_exec_toStmt`): the run of a first-order
statement in the environment of the values of $\sigma$ is the current run of its instantiation by
$\sigma$. So every lemma and every invariant of `exec` holds for `Prog.exec` by one rewrite; the
invariants are restated here for programs. A `whileFuel` loop tests its comparison at most `fuel`
times and fails if every test it makes holds, so a successful run executes its body at most
`fuel - 1` times. Design: `docs/design/Computation.md`, "First-order programs and target
statements" (F3, F7).

## Main definitions

* `NLAlib.Computation.FStmt.exec`, `NLAlib.Computation.Prog.exec`: the run.
* `NLAlib.Computation.Prog.RunsWithin`: a run within a budget.

## Main results

* `NLAlib.Computation.FStmt.exec_eq_exec_toStmt`, `NLAlib.Computation.Prog.exec_eq_exec_toStmt`:
  the bridge to the run of the instantiated statement.
* `NLAlib.Computation.Prog.runsWithin_iff`: a program runs within a budget if and only if its
  instantiation does.
* `NLAlib.Computation.Prog.cnt_le_of_exec_eq_some`,
  `NLAlib.Computation.Prog.cur_eq_of_exec_eq_some`,
  `NLAlib.Computation.Prog.shape_eq_of_exec_eq_some`,
  `NLAlib.Computation.Prog.peak_le_of_exec_eq_some`: the counts and peaks of a run only grow,
  and it frees exactly what it allocates.
* `NLAlib.Computation.Prog.store_eq_of_exec_eq_some_of_cnt_le`,
  `NLAlib.Computation.Prog.pos_eq_of_exec_eq_some_of_cnt_le`: a run that charges nothing writes
  and draws nothing.
* `NLAlib.Computation.Prog.exec_eq_of_exec_eq_some_of_cnt_load_le`: a run that makes no oracle
  call is the same under any oracle.
-/

@[expose] public section

namespace NLAlib.Computation

/-! ### The run -/

section Run

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C)

/-- **The run of a first-order statement** under `I`, in an environment of handles `ρB` and of
index values `ρI`. The leaves (instructions, oracle calls, read-only reads, comparisons) run by
the rules of `NLAlib.Computation.exec`, with each index expression evaluated in the environment;
`alloc` binds the new handle `st.store.size` and `loop` the iteration index. A `whileFuel` loop
tests its comparison at most `fuel` times and fails if every test it makes holds. -/
def FStmt.exec : {nb ni : ℕ} → FStmt P ι nb ni → (Fin nb → ℕ) → (Fin ni → ℕ) →
    St P K C → Option (St P K C)
  | _, _, .skip, _, _, st => some st
  | _, _, .seq s t, ρB, ρI, st => (s.exec ρB ρI st).bind (t.exec ρB ρI)
  | _, _, .instr i, ρB, ρI, st =>
      let i' := i.subst ρB fun v => .const (ρI v)
      (i'.run I.sem I.tape st.store st.pos).map fun r =>
        { st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i'.kind }
  | _, _, .apply o p d dOff s sOff cols, ρB, ρI, st =>
      let L := I.height o * cols.evalIn ρI
      if ρB d ≠ ρB s ∨ dOff.evalIn ρI + L ≤ sOff.evalIn ρI ∨
          sOff.evalIn ρI + L ≤ dOff.evalIn ρI then
        (st.store.readBlock p (ρB s) (sOff.evalIn ρI) L).bind fun X =>
          (I.oracle o (cols.evalIn ρI) X).bind fun Y =>
            (st.store.writeBlock p (ρB d) (dOff.evalIn ρI) Y).map fun s' => { st with
              store := s'
              cnt := st.cnt + (I.charge (.load p o) + cols.evalIn ρI • I.charge (.matvec p o)) }
      else none
  | _, _, .rom p d i, ρB, ρI, st => (I.rom (i.evalIn ρI)).bind fun v =>
      (st.store.write p (ρB d.buf) (d.idx.evalIn ρI) v).map fun s' =>
        { st with store := s', cnt := st.cnt + I.charge (.rom p) }
  | _, _, .alloc p len body, ρB, ρI, st =>
      let n := len.evalIn ρI
      (body.exec (Fin.snoc (α := fun _ => ℕ) ρB st.store.size) ρI { st with
          store := st.store.push (p, Array.replicate n none),
          cur := Function.update st.cur p (st.cur p + n),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + n)),
          curW := st.curW + n * I.width p,
          peakW := max st.peakW (st.curW + n * I.width p) }).map
        fun st₂ => { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - n)
          curW := st₂.curW - n * I.width p }
  | _, _, .loop n body, ρB, ρI, st =>
      (List.range (n.evalIn ρI)).foldlM
        (fun st i => body.exec ρB (Fin.snoc (α := fun _ => ℕ) ρI i) st) st
  | _, _, .whileFuel fuel p c x y body, ρB, ρI, st =>
      ((List.range (fuel.evalIn ρI)).foldlM (fun (s : St P K C × Bool) _ =>
        if s.2 then (cmpStep I p c (x.subst ρB fun v => .const (ρI v))
            (y.subst ρB fun v => .const (ρI v)) s.1).bind fun r =>
          if r.1 then (body.exec ρB ρI r.2).map fun st' => (st', true) else some (r.2, false)
        else some s) (st, true)).bind fun r => if r.2 then none else some r.1
  | _, _, .ite p c x y t e, ρB, ρI, st =>
      (cmpStep I p c (x.subst ρB fun v => .const (ρI v)) (y.subst ρB fun v => .const (ρI v))
        st).bind fun r => if r.1 then t.exec ρB ρI r.2 else e.exec ρB ρI r.2
  | _, _, .named _ _ body, ρB, ρI, st => body.exec ρB ρI st

/-- **The run of a program** at the sizes $N$ and $n$: declared buffer $j$ at handle $j$, the
oracle dimension $N$ as index variable $0$ and size $i$ as index variable $i + 1$. -/
def Prog.exec {r b : ℕ} (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ) (st : St P K C) :
    Option (St P K C) :=
  FStmt.exec I prog (fun j => (j : ℕ)) (Fin.cons N n) st

end Run

/-! ### The bridge to the run of the instantiated statement -/

section Bridge

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C)

/-- An instruction runs the same under two substitutions of index expressions with the same
values. -/
theorem Instr.run_subst_congr {nb ni : ℕ} (i : Instr P (Fin nb) (Fin ni)) (f : Fin nb → ℕ)
    {σ σ' : Fin ni → IExp ℕ} (h : ∀ v, (σ v).eval = (σ' v).eval) (sem : ScalarSem P K)
    (tape : Dist → ℕ → K) (s : Store P K) (pos : Dist → ℕ) :
    (i.subst f σ).run sem tape s pos = (i.subst f σ').run sem tape s pos := by
  have h' : (fun v => (σ v).eval) = fun v => (σ' v).eval := funext h
  cases i <;> simp only [Instr.subst, Cell.subst, Instr.run, IExp.eval_subst, h']

omit [DecidableEq P] in
/-- The kind of an instruction does not depend on its index expressions. -/
theorem Instr.kind_subst {nb ni : ℕ} (i : Instr P (Fin nb) (Fin ni)) (f : Fin nb → ℕ)
    (σ σ' : Fin ni → IExp ℕ) :
    Instr.kind (ι := ι) (i.subst f σ) = Instr.kind (i.subst f σ') := by
  cases i <;> rfl

/-- A comparison runs the same under two substitutions of index expressions with the same
values. -/
theorem cmpStep_subst_congr {nb ni : ℕ} (p : P) (c : CmpOp) (x y : Cell (Fin nb) (Fin ni))
    (f : Fin nb → ℕ) {σ σ' : Fin ni → IExp ℕ} (h : ∀ v, (σ v).eval = (σ' v).eval)
    (st : St P K C) :
    cmpStep I p c (x.subst f σ) (y.subst f σ) st =
      cmpStep I p c (x.subst f σ') (y.subst f σ') st := by
  have h' : (fun v => (σ v).eval) = fun v => (σ' v).eval := funext h
  simp only [cmpStep, Cell.subst, IExp.eval_subst, h']

omit [DecidableEq P] [AddMonoid C] in
/-- The values of the substitution under a loop binder. -/
private theorem eval_snoc {ni : ℕ} (σ : Fin ni → IExp ℕ) (i : ℕ) :
    (fun v => (Fin.snoc (α := fun _ => IExp ℕ) σ (.var i) v).eval) =
      Fin.snoc (α := fun _ => ℕ) (fun v => (σ v).eval) i := by
  funext v
  refine Fin.lastCases ?_ (fun j => ?_) v <;> simp

/-- The bridge: the run of a first-order statement in the environment of the values of the
index expressions $\sigma$ is the current run of its instantiation by $\sigma$. -/
theorem FStmt.exec_eq_exec_toStmt : ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρB : Fin nb → ℕ)
    (σ : Fin ni → IExp ℕ) (st : St P K C),
    s.exec I ρB (fun v => (σ v).eval) st = Computation.exec I (s.toStmt ρB σ) st
  | _, _, .skip, _, _, st => by rw [FStmt.exec, FStmt.toStmt, Computation.exec]
  | _, _, .seq s t, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec, s.exec_eq_exec_toStmt ρB σ st]
      congr 1; funext st'; exact t.exec_eq_exec_toStmt ρB σ st'
  | _, _, .instr i, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec,
        Instr.run_subst_congr i ρB (σ' := σ) (fun v => by simp)]
      rw [Instr.kind_subst i ρB (fun v => .const (σ v).eval) σ]
  | _, _, .apply o p d dOff s sOff cols, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [IExp.eval_subst]
  | _, _, .rom p d i, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [Cell.subst, IExp.eval_subst]
  | _, _, .alloc p len body, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [IExp.eval_subst]
      rw [body.exec_eq_exec_toStmt]
  | _, _, .loop n body, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [IExp.eval_subst]
      congr 1; funext st' i
      rw [← eval_snoc, body.exec_eq_exec_toStmt]
  | _, _, .whileFuel fuel p c x y body, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [IExp.eval_subst]
      congr 2; funext s' _
      rw [cmpStep_subst_congr I p c x y ρB (σ' := σ) (fun v => by simp)]
      simp only [body.exec_eq_exec_toStmt]
  | _, _, .ite p c x y t e, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec,
        cmpStep_subst_congr I p c x y ρB (σ' := σ) (fun v => by simp)]
      congr 1; funext r
      rw [t.exec_eq_exec_toStmt, e.exec_eq_exec_toStmt]
  | _, _, .named _ _ body, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec, body.exec_eq_exec_toStmt]

/-- The bridge for programs: the run of a program at the sizes $N$ and $n$ is the current
run of its instantiation at these sizes. -/
theorem Prog.exec_eq_exec_toStmt {r b : ℕ} (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ)
    (st : St P K C) : prog.exec I N n st = Computation.exec I (prog.toStmt N n) st := by
  rw [Prog.exec, Prog.toStmt, ← FStmt.exec_eq_exec_toStmt]
  congr 1
  funext v
  refine Fin.cases ?_ (fun j => ?_) v <;> simp

end Bridge

/-! ### Running within a budget -/

section Budget

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Preorder C]

/-- **A run of a program within a budget**: the run of `prog` at the sizes $N$ and $n$ from
`st₀` under `I` succeeds in a state `st` whose counts are at most `c` more than at the start,
whose peak memory plus the read-only data is at most `m p` cells at each tag `p`, and which
satisfies `Q`. -/
def Prog.RunsWithin {r b : ℕ} (I : Interp P ι K C) (prog : Prog P ι r b) (N : ℕ)
    (n : Fin r → ℕ) (st₀ : St P K C) (c : C) (m : P → ℕ) (Q : St P K C → Prop) : Prop :=
  ∃ st, prog.exec I N n st₀ = some st ∧ st.cnt ≤ st₀.cnt + c ∧
    (∀ q, st.peak q + I.romSize q ≤ m q) ∧ Q st

/-- A program runs within a budget if and only if its instantiation at the same sizes does. -/
theorem Prog.runsWithin_iff {r b : ℕ} (I : Interp P ι K C) (prog : Prog P ι r b) (N : ℕ)
    (n : Fin r → ℕ) (st₀ : St P K C) (c : C) (m : P → ℕ) (Q : St P K C → Prop) :
    prog.RunsWithin I N n st₀ c m Q ↔ Computation.RunsWithin I (prog.toStmt N n) st₀ c m Q := by
  simp only [Prog.RunsWithin, Computation.RunsWithin, Prog.exec_eq_exec_toStmt]

end Budget

/-! ### Invariants of the run -/

section Invariants

variable {P ι K : Type} [DecidableEq P] {I : Interp P ι K (OpCount P ι)} {r b : ℕ}
  {prog : Prog P ι r b} {N : ℕ} {n : Fin r → ℕ} {st st' : St P K (OpCount P ι)}

/-- The counts of a run of a program only grow. -/
theorem Prog.cnt_le_of_exec_eq_some (h : prog.exec I N n st = some st') : st.cnt ≤ st'.cnt :=
  Computation.cnt_le_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- Every allocation of a program is freed: a run ends with the current memory in cells, at
every tag, of its start. -/
theorem Prog.cur_eq_of_exec_eq_some (h : prog.exec I N n st = some st') : st'.cur = st.cur :=
  Computation.cur_eq_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- A run of a program ends with the current memory in bits of its start. -/
theorem Prog.curW_eq_of_exec_eq_some (h : prog.exec I N n st = some st') :
    st'.curW = st.curW :=
  Computation.curW_eq_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- A run of a program frees exactly what it allocates: it ends with the shape of the store of
its start. -/
theorem Prog.shape_eq_of_exec_eq_some (h : prog.exec I N n st = some st') :
    st'.store.shape = st.store.shape :=
  Computation.shape_eq_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- The peak memory in cells of a run of a program only grows. -/
theorem Prog.peak_le_of_exec_eq_some (h : prog.exec I N n st = some st') :
    st.peak ≤ st'.peak :=
  Computation.peak_le_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- The peak memory in bits of a run of a program only grows. -/
theorem Prog.peakW_le_of_exec_eq_some (h : prog.exec I N n st = some st') :
    st.peakW ≤ st'.peakW :=
  Computation.peakW_le_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- Every write of a program is charged: if no operation kind is free, a run whose counts do not
grow leaves the store unchanged. -/
theorem Prog.store_eq_of_exec_eq_some_of_cnt_le (hc : ∀ k, I.charge k ≠ 0)
    (h : prog.exec I N n st = some st') (hcnt : st'.cnt ≤ st.cnt) : st'.store = st.store :=
  Computation.store_eq_of_exec_eq_some_of_cnt_le hc
    ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h) hcnt

/-- Every draw of a program is charged: if no operation kind is free, a run whose counts do not
grow leaves the tape positions unchanged. -/
theorem Prog.pos_eq_of_exec_eq_some_of_cnt_le (hc : ∀ k, I.charge k ≠ 0)
    (h : prog.exec I N n st = some st') (hcnt : st'.cnt ≤ st.cnt) : st'.pos = st.pos :=
  Computation.pos_eq_of_exec_eq_some_of_cnt_le hc
    ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h) hcnt

/-- The oracle is a program's only access to the matrix: under the standard charge, a run that
makes no oracle call (its load counts do not grow) is the same run under any other oracle. -/
theorem Prog.exec_eq_of_exec_eq_some_of_cnt_load_le (hc : ∀ k, I.charge k = Finsupp.single k 1)
    (O : ι → ℕ → Array K → Option (Array K)) (h : prog.exec I N n st = some st')
    (hl : ∀ p o, st'.cnt (.load p o) ≤ st.cnt (.load p o)) :
    prog.exec { I with oracle := O } N n st = some st' := by
  rw [Prog.exec_eq_exec_toStmt] at h ⊢
  exact Computation.exec_eq_of_exec_eq_some_of_cnt_load_le hc O _ h hl

end Invariants

end NLAlib.Computation
