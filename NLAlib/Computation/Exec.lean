/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Group.Nat
public import NLAlib.Computation.Store
public import NLAlib.Computation.Syntax

/-!
# Running a program

The run `NLAlib.Computation.exec I s st` of a statement `s` (at `VB := ℕ`, `VI := ℕ`) from a
state `st` under an interpretation `I` is a deterministic function into `Option`: `none` marks a
failure (an operation outside its domain, an uninitialised read, an index out of bounds, a tag
mismatch, an invalid or aliased oracle call, running out of fuel). The interpretation holds the
value semantics of the scalar operations (`NLAlib.Computation.ScalarSem`), the charge of each
operation kind, the random tape of each distribution, the oracles, the read-only data and its
size, and the width in bits of a cell of each tag. The state holds the store
(`NLAlib.Computation.Store`, a stack of tagged buffers of possibly uninitialised cells), the tape
positions, the counts, and the current and peak memory in cells per tag and in bits.

The run lemmas unfold `exec` one constructor at a time, and run a loop by an invariant and a
sequence of draws from the tape. Design: `docs/design/Computation.md` (D3, D8, D11, D12, D17).

## Main definitions

* `NLAlib.Computation.OpKind`, `NLAlib.Computation.OpCount`: operation kinds and counts.
* `NLAlib.Computation.ScalarSem`: a value semantics; `NLAlib.Computation.Interp`: an
  interpretation.
* `NLAlib.Computation.St`: the state.
* `NLAlib.Computation.exec`: the run.

## Main results

* `NLAlib.Computation.exec_seq`, `NLAlib.Computation.exec_loop`,
  `NLAlib.Computation.exec_alloc`: the run of a sequence, a loop (a fold) and an allocation.
* `NLAlib.Computation.exists_exec_loop_eq_some_of_forall`: a loop run by an invariant.
* `NLAlib.Computation.exec_forRange_draw`: a loop of draws writes consecutive tape values.
-/

@[expose] public section

namespace NLAlib.Computation

/-! ### Counts and semantics -/

/-- The kinds of operations a run counts: binary and unary operations, literals, comparisons,
copies and conversions per tag, draws per tag and distribution, read-only reads per tag, and the
loads and matrix-vector products of each oracle per tag. -/
inductive OpKind (P ι : Type) where
  /-- A binary operation at a tag. -/
  | bin (p : P) (b : BinOp)
  /-- A unary operation at a tag. -/
  | un (p : P) (u : UnOp)
  /-- A literal at a tag. -/
  | lit (p : P)
  /-- A comparison at a tag. -/
  | cmp (p : P)
  /-- A copy at a tag. -/
  | copy (p : P)
  /-- A draw at a tag from a distribution. -/
  | draw (p : P) (d : Dist)
  /-- A conversion from one tag to another. -/
  | convert (p q : P)
  /-- A read of the read-only data at a tag. -/
  | rom (p : P)
  /-- One oracle call at a tag (a load of the matrix). -/
  | load (p : P) (o : ι)
  /-- One matrix-vector product of an oracle call at a tag. -/
  | matvec (p : P) (o : ι)

/-- Counts of operations: finitely supported functions on the kinds. A weighted total (flops, bit
operations) is Mathlib's `Finsupp.weight`. -/
abbrev OpCount (P ι : Type) := OpKind P ι →₀ ℕ

/-- A value semantics over the carrier `K`: each scalar operation at a tag, partial (`none` marks
an operation outside its domain, such as a division by zero). -/
structure ScalarSem (P K : Type) where
  /-- The value of a rational literal. -/
  lit : P → ℚ → Option K
  /-- A binary operation. -/
  bin : P → BinOp → K → K → Option K
  /-- A unary operation. -/
  un : P → UnOp → K → Option K
  /-- A comparison. -/
  cmp : P → CmpOp → K → K → Option Bool
  /-- A conversion from one tag to another. -/
  convert : P → P → K → Option K

/-- The value of a closed index expression. -/
def IExp.eval : IExp ℕ → ℕ
  | .var v => v
  | .const n => n
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .mod a b => a.eval % b.eval

/-- The value of a variable. -/
@[simp] theorem IExp.eval_var (v : ℕ) : (IExp.var v).eval = v := rfl

/-- The value of a constant. -/
@[simp] theorem IExp.eval_const (n : ℕ) : (IExp.const n).eval = n := rfl

/-- The value of the numeral `0` (a case of `NLAlib.Computation.IExp.eval_ofNat`). -/
theorem IExp.eval_zero : (0 : IExp ℕ).eval = 0 := rfl

/-- The value of the numeral `1` (a case of `NLAlib.Computation.IExp.eval_ofNat`). -/
theorem IExp.eval_one : (1 : IExp ℕ).eval = 1 := rfl

/-- The value of a numeral; every numeral, $0$ and $1$ included, is a constant. -/
@[simp] theorem IExp.eval_ofNat (n : ℕ) :
    (no_index (OfNat.ofNat n : IExp ℕ)).eval = OfNat.ofNat n := rfl

/-- The value of a sum. -/
@[simp] theorem IExp.eval_add (a b : IExp ℕ) : (a + b).eval = a.eval + b.eval := rfl

/-- The value of a truncated difference. -/
@[simp] theorem IExp.eval_sub (a b : IExp ℕ) : (a - b).eval = a.eval - b.eval := rfl

/-- The value of a product. -/
@[simp] theorem IExp.eval_mul (a b : IExp ℕ) : (a * b).eval = a.eval * b.eval := rfl

/-- The value of a remainder. -/
@[simp] theorem IExp.eval_mod (a b : IExp ℕ) : (a % b).eval = a.eval % b.eval := rfl

/-! ### States and interpretations -/

/-- The state of a run: the store, the tape position of each distribution, the counts, and the
current and peak memory, in cells per tag and in bits over all tags. -/
structure St (P K C : Type) where
  /-- The store. -/
  store : Store P K
  /-- The next tape position of each distribution. -/
  pos : Dist → ℕ
  /-- The counts. -/
  cnt : C
  /-- Current memory in cells, per tag. -/
  cur : P → ℕ
  /-- Peak memory in cells, per tag. -/
  peak : P → ℕ
  /-- Current memory in bits, over all tags. -/
  curW : ℕ
  /-- Peak memory in bits, over all tags. -/
  peakW : ℕ

/-- An interpretation: the value semantics, the charge of each kind, the tapes, the oracles
(partial: `none` marks an invalid query), their heights, the read-only data, its size per tag, and
the width in bits of a cell of each tag. -/
structure Interp (P ι K C : Type) where
  /-- The value semantics. -/
  sem : ScalarSem P K
  /-- The charge of one operation of each kind. -/
  charge : OpKind P ι → C
  /-- The tape of each distribution. -/
  tape : Dist → ℕ → K
  /-- The oracles: a block of `cols` columns, stored column-major, to its product. -/
  oracle : ι → ℕ → Array K → Option (Array K)
  /-- The number of rows of the matrix of each oracle. -/
  height : ι → ℕ
  /-- The read-only data. -/
  rom : ℕ → Option K
  /-- The size of the read-only data per tag: constant memory. -/
  romSize : P → ℕ
  /-- Bits per cell at each tag (for memory in bits). -/
  width : P → ℕ

section Exec

variable {P ι K C : Type} [DecidableEq P]

/-- The kind of an instruction, independent of the interpretation. -/
def Instr.kind {ι : Type} : Instr P ℕ ℕ → OpKind P ι
  | .lit p _ _ => .lit p
  | .litIdx p _ _ => .lit p
  | .bin p b _ _ _ => .bin p b
  | .un p u _ _ => .un p u
  | .copy p _ _ => .copy p
  | .draw p d _ => .draw p d
  | .convert p q _ _ => .convert p q

/-- One instruction on the store and the tape positions. -/
def Instr.run (sem : ScalarSem P K) (tape : Dist → ℕ → K) (s : Store P K) (pos : Dist → ℕ) :
    Instr P ℕ ℕ → Option (Store P K × (Dist → ℕ))
  | .lit p dst q => (sem.lit p q).bind fun v =>
      (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .litIdx p dst e => (sem.lit p (e.eval : ℚ)).bind fun v =>
      (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .bin p b dst x y => (s.read p x.buf x.idx.eval).bind fun a =>
      (s.read p y.buf y.idx.eval).bind fun c => (sem.bin p b a c).bind fun v =>
        (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .un p u dst x => (s.read p x.buf x.idx.eval).bind fun a => (sem.un p u a).bind fun v =>
      (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .copy p dst src => (s.read p src.buf src.idx.eval).bind fun v =>
      (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .draw p d dst => (s.write p dst.buf dst.idx.eval (tape d (pos d))).map fun s' =>
      (s', Function.update pos d (pos d + 1))
  | .convert p q dst src => (s.read p src.buf src.idx.eval).bind fun a =>
      (sem.convert p q a).bind fun v =>
        (s.write q dst.buf dst.idx.eval v).map fun s' => (s', pos)

variable [AddMonoid C] (I : Interp P ι K C)

/-- One comparison: the outcome and the charged state. -/
def cmpStep (p : P) (c : CmpOp) (x y : Cell ℕ ℕ) (st : St P K C) : Option (Bool × St P K C) :=
  (st.store.read p x.buf x.idx.eval).bind fun a => (st.store.read p y.buf y.idx.eval).bind
    fun b => (I.sem.cmp p c a b).map fun r => (r, { st with cnt := st.cnt + I.charge (.cmp p) })

/-- **The run** of a statement under an interpretation. An allocation pushes a fresh buffer of
uninitialised cells, raises the current and peak memory, runs the body with the new buffer's
handle (its position in the stack) and pops the buffer. An oracle call reads the source block,
charges one load and one matrix-vector product per column, and writes the product; it fails if
the source and destination blocks overlap (an aliased call, which no implementation with bounded
scratch can serve). -/
def exec : Stmt P ι ℕ ℕ → St P K C → Option (St P K C)
  | .skip, st => some st
  | .seq s t, st => (exec s st).bind (exec t)
  | .instr i, st => (i.run I.sem I.tape st.store st.pos).map fun r =>
      { st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i.kind }
  | .apply o p dst dOff src sOff cols, st =>
      if dst ≠ src ∨ dOff.eval + I.height o * cols.eval ≤ sOff.eval ∨
          sOff.eval + I.height o * cols.eval ≤ dOff.eval then
        (st.store.readBlock p src sOff.eval (I.height o * cols.eval)).bind fun X =>
          (I.oracle o cols.eval X).bind fun Y => (st.store.writeBlock p dst dOff.eval Y).map
            fun s => { st with
              store := s
              cnt := st.cnt + (I.charge (.load p o) + cols.eval • I.charge (.matvec p o)) }
      else none
  | .rom p dst i, st => (I.rom i.eval).bind fun v =>
      (st.store.write p dst.buf dst.idx.eval v).map fun s =>
        { st with
          store := s
          cnt := st.cnt + I.charge (.rom p) }
  | .alloc p len body, st =>
      (exec (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) }).map
        fun st₂ => { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p }
  | .loop n body, st => (List.range n.eval).foldlM (fun st i => exec (body i) st) st
  | .whileFuel fuel p c x y body, st =>
      ((List.range fuel.eval).foldlM (fun (s : St P K C × Bool) _ =>
        if s.2 then (cmpStep I p c x y s.1).bind fun r =>
          if r.1 then (exec body r.2).map fun st' => (st', true) else some (r.2, false)
        else some s) (st, true)).bind fun r => if r.2 then none else some r.1
  | .ite p c x y t e, st => (cmpStep I p c x y st).bind fun r =>
      if r.1 then exec t r.2 else exec e r.2
  | .named _ _ body, st => exec body st

/-! ### Run lemmas -/

/-- The run of a sequence. -/
theorem exec_seq (s t : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.seq s t) st = (exec I s st).bind (exec I t) := by
  rw [exec]

/-- The run of a loop is a fold over the indices. -/
theorem exec_loop (n : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.loop n body) st = (List.range n.eval).foldlM (fun st i => exec I (body i) st) st := by
  rw [exec]

/-- The run of a named kernel is the run of its body. -/
theorem exec_named (name : String) (args : List (Arg ℕ ℕ)) (body : Stmt P ι ℕ ℕ)
    (st : St P K C) : exec I (.named name args body) st = exec I body st := by
  rw [exec]

/-- The run of an allocation: push a fresh buffer, run the body on its handle, pop it. -/
theorem exec_alloc (p : P) (len : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.alloc p len body) st =
      (exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) }).map
        fun st₂ => { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p } := by
  rw [exec]

/-- The run of a conditional. -/
theorem exec_ite (p : P) (c : CmpOp) (x y : Cell ℕ ℕ) (t e : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.ite p c x y t e) st =
      (cmpStep I p c x y st).bind fun r => if r.1 then exec I t r.2 else exec I e r.2 := by
  rw [exec]

/-- The run of a scalar instruction. -/
theorem exec_instr (i : Instr P ℕ ℕ) (st : St P K C) :
    exec I (.instr i) st = (i.run I.sem I.tape st.store st.pos).map fun r =>
      { st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i.kind } := by
  rw [exec]

/-- The run of a statement followed by `skip` is the run of the statement. -/
theorem exec_seq_skip (s : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.seq s .skip) st = exec I s st := by
  rw [exec_seq]
  rcases exec I s st with _ | st'
  · rfl
  · change exec I .skip st' = some st'
    rw [exec]

/-- The run of a sequence whose first part succeeds: the run of the second part from there. -/
theorem exec_seq_of_exec_eq_some {s t : Stmt P ι ℕ ℕ} {st st₁ : St P K C}
    (h : exec I s st = some st₁) : exec I (.seq s t) st = exec I t st₁ := by
  rw [exec_seq, h, Option.bind_some]

/-- The run of a builder that emits one statement before its continuation (a kernel, a loop, a
conditional, a block), followed by `f`: the run of the first, then the run of `f`. -/
theorem exec_run_bind {b : Builder P ι ℕ ℕ Unit} {X : Stmt P ι ℕ ℕ}
    (hb : ∀ k, ContT.run b k = .seq X (k ())) (f : Unit → Builder P ι ℕ ℕ Unit)
    (st : St P K C) : exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run) := by
  have h1 : (b >>= f).run = .seq X (f ()).run := hb _
  have h2 : b.run = .seq X .skip := hb _
  rw [h1, h2, exec_seq, exec_seq_skip]

/-- A loop invariant: if `R 0` holds at the start and, for each index `i` below the bound,
the body run from a state satisfying `R i` succeeds in a state satisfying `R (i + 1)`, the loop
succeeds in a state satisfying `R n`. -/
theorem exists_exec_loop_eq_some_of_forall {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st : St P K C} (R : ℕ → St P K C → Prop) (h0 : R 0 st)
    (hstep : ∀ i < n.eval, ∀ st, R i st → ∃ st', exec I (body i) st = some st' ∧ R (i + 1) st') :
    ∃ st', exec I (.loop n body) st = some st' ∧ R n.eval st' := by
  rw [exec_loop]
  generalize n.eval = m at hstep ⊢
  induction m with
  | zero => exact ⟨st, rfl, h0⟩
  | succ m ih =>
    obtain ⟨st₁, h₁, hR₁⟩ := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    obtain ⟨st₂, h₂, hR₂⟩ := hstep m (Nat.lt_succ_self m) st₁ hR₁
    refine ⟨st₂, ?_, hR₂⟩
    rw [List.range_succ, List.foldlM_append, h₁]
    simpa using h₂

/-- The run of `skip`. -/
theorem exec_skip (st : St P K C) : exec I .skip st = some st := by
  rw [exec]

/-- The run of a literal, then the rest. -/
theorem exec_seq_instr_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ} {st : St P K C}
    {v : K} {s : Store P K} (hv : I.sem.lit p q = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.lit p dst q)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.lit p) } := by
  simp [exec_seq, exec_instr, Instr.run, hv, hw, Instr.kind]

/-- The run of an index literal, then the rest. -/
theorem exec_seq_instr_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {st : St P K C} {v : K} {s : Store P K} (hv : I.sem.lit p (e.eval : ℚ) = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.litIdx p dst e)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.lit p) } := by
  simp [exec_seq, exec_instr, Instr.run, hv, hw, Instr.kind]

/-- The run of a binary operation, then the rest. -/
theorem exec_seq_instr_bin {p : P} {b : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {st : St P K C} {a c v : K} {s : Store P K}
    (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some c) (hv : I.sem.bin p b a c = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.bin p b dst x y)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.bin p b) } := by
  simp [exec_seq, exec_instr, Instr.run, hx, hy, hv, hw, Instr.kind]

/-- The run of a unary operation, then the rest. -/
theorem exec_seq_instr_un {p : P} {u : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {st : St P K C} {a v : K} {s : Store P K} (hx : st.store.read p x.buf x.idx.eval = some a)
    (hv : I.sem.un p u a = some v) (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.un p u dst x)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.un p u) } := by
  simp [exec_seq, exec_instr, Instr.run, hx, hv, hw, Instr.kind]

/-- The run of a copy, then the rest. -/
theorem exec_seq_instr_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ} {st : St P K C}
    {v : K} {s : Store P K} (hx : st.store.read p src.buf src.idx.eval = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.copy p dst src)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.copy p) } := by
  simp [exec_seq, exec_instr, Instr.run, hx, hw, Instr.kind]

/-- The run of a draw, then the rest: the next tape value, and the tape position advances. -/
theorem exec_seq_instr_draw {p : P} {d : Dist} {dst : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {st : St P K C} {s : Store P K}
    (hw : st.store.write p dst.buf dst.idx.eval (I.tape d (st.pos d)) = some s) :
    exec I (.seq (.instr (.draw p d dst)) t) st =
      exec I t { st with
        store := s
        pos := Function.update st.pos d (st.pos d + 1)
        cnt := st.cnt + I.charge (.draw p d) } := by
  simp [exec_seq, exec_instr, Instr.run, hw, Instr.kind]

/-- A loop of draws writes consecutive tape values: the loop that draws cell `idx i` of
buffer `X` from the tape of `d`, where `idx i` evaluates to $\mathit{off} + i$, for $i < n$,
succeeds from a state in which each of these cells can be written; cell $\mathit{off} + i$ then
holds the tape value at position $\mathit{pos}(d) + i$, every other cell, the shape and the
memory are kept, the tape position of `d` advances by $n$, and the run counts $n$ draws. -/
theorem exec_forRange_draw (p : P) (d : Dist) (X off : ℕ) (n : IExp ℕ) (idx : ℕ → IExp ℕ)
    (hidx : ∀ i, (idx i).eval = off + i) (st : St P K C)
    (hw : ∀ i < n.eval, ∃ v s, st.store.write p X (off + i) v = some s) :
    ∃ st', exec I (Builder.forRange n fun i => Builder.ins (.draw p d ⟨X, idx i⟩)).run st =
        some st' ∧
      (∀ i < n.eval, st'.store.read p X (off + i) = some (I.tape d (st.pos d + i))) ∧
      (∀ q b j, (b = X → j < off ∨ off + n.eval ≤ j) →
        st'.store.read q b j = st.store.read q b j) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = Function.update st.pos d (st.pos d + n.eval) ∧
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW ∧
      st'.cnt = st.cnt + n.eval • I.charge (.draw p d) := by
  rw [show (Builder.forRange (ι := ι) n fun i => Builder.ins (.draw p d ⟨X, idx i⟩)).run =
    .seq (.loop n fun i => (Builder.ins (.draw p d ⟨X, idx i⟩)).run) .skip from rfl,
    exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall I (fun i st' =>
      (∀ i' < i, st'.store.read p X (off + i') = some (I.tape d (st.pos d + i'))) ∧
      (∀ q b j, (b = X → j < off ∨ off + i ≤ j) → st'.store.read q b j = st.store.read q b j) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = Function.update st.pos d (st.pos d + i) ∧
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW ∧
      st'.cnt = st.cnt + i • I.charge (.draw p d))
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl, rfl, by simp, rfl, rfl, rfl,
      rfl, by simp⟩ ?_
  intro i hi st' ⟨hrd, hfr, hsh, hpos, hcur, hpeak, hcurW, hpeakW, hcnt⟩
  obtain ⟨v₀, s₀, hs₀⟩ := hw i hi
  obtain ⟨s, hs⟩ := Store.exists_write_eq_some_of_shape_eq hsh hs₀ (I.tape d (st'.pos d))
  have hpd : st'.pos d = st.pos d + i := by rw [hpos]; simp
  refine ⟨_, (exec_seq_instr_draw I (by rw [hidx]; exact hs)).trans (exec_skip I _),
    fun i' hi' => ?_, fun q b j hb => ?_, ?_, ?_, hcur, hpeak, hcurW, hpeakW, ?_⟩
  · change s.read p X (off + i') = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
    · rw [Store.read_of_write_eq_some_of_ne hs (Or.inr (by omega)), hrd i' h]
    · rw [Store.read_of_write_eq_some hs, hpd]
  · change s.read q b j = _
    rw [Store.read_of_write_eq_some_of_ne hs ?_, hfr q b j ?_]
    · intro h; rcases hb h with h' | h' <;> omega
    · by_cases h : b = X
      · exact Or.inr (by rcases hb h with h' | h' <;> omega)
      · exact Or.inl h
  · exact (Store.shape_of_write_eq_some hs).trans hsh
  · change Function.update st'.pos d (st'.pos d + 1) = _
    rw [hpd, hpos, Function.update_idem, Nat.add_assoc]
  · change st'.cnt + I.charge (.draw p d) = _
    rw [hcnt, succ_nsmul, add_assoc]

end Exec

end NLAlib.Computation
