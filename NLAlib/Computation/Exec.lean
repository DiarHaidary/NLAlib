/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Group.Nat
public import NLAlib.Computation.Syntax

/-!
# Running a program

The run `NLAlib.Computation.exec I s st` of a statement `s` (at `VB := ℕ`, `VI := ℕ`) from a
state `st` under an interpretation `I` is a deterministic function into `Option`: `none` marks a
failure (an operation outside its domain, an uninitialised read, an index out of bounds, a tag
mismatch, an invalid or aliased oracle call, running out of fuel). The interpretation holds the
value semantics of the scalar operations (`NLAlib.Computation.ScalarSem`), the charge of each
operation kind, the random tape of each distribution, the oracles, the read-only data and its
size, and the width in bits of a cell of each tag. The state holds the store, a stack of tagged
buffers of possibly uninitialised cells, the tape positions, the counts, and the current and peak
memory in cells per tag and in bits.

The run lemmas unfold `exec` one constructor at a time; the store lemmas say what a read sees after
a write, an allocation or a block write. Design: `docs/design/Computation.md` (D3, D8, D11, D17).

## Main definitions

* `NLAlib.Computation.OpKind`, `NLAlib.Computation.OpCount`: operation kinds and counts.
* `NLAlib.Computation.ScalarSem`: a value semantics; `NLAlib.Computation.Interp`: an
  interpretation.
* `NLAlib.Computation.Store`, `NLAlib.Computation.St`: the store and the state.
* `NLAlib.Computation.exec`: the run.

## Main results

* `NLAlib.Computation.exec_seq`, `NLAlib.Computation.exec_loop`,
  `NLAlib.Computation.exec_alloc`: the run of a sequence, a loop (a fold) and an allocation.
* `NLAlib.Computation.Store.read_of_write_eq_some`,
  `NLAlib.Computation.Store.read_of_write_eq_some_of_ne`: a read after a write.
* `NLAlib.Computation.Store.read_of_writeBlock_eq_some_of_lt`,
  `NLAlib.Computation.Store.read_of_writeBlock_eq_some_of_ne`: a read after a block write.
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

/-- The value of the numeral `0`. -/
@[simp] theorem IExp.eval_zero : (0 : IExp ℕ).eval = 0 := rfl

/-- The value of the numeral `1`. -/
@[simp] theorem IExp.eval_one : (1 : IExp ℕ).eval = 1 := rfl

/-- The value of a numeral. -/
@[simp] theorem IExp.eval_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : IExp ℕ)).eval = OfNat.ofNat n := rfl

/-- The value of a sum. -/
@[simp] theorem IExp.eval_add (a b : IExp ℕ) : (a + b).eval = a.eval + b.eval := rfl

/-- The value of a truncated difference. -/
@[simp] theorem IExp.eval_sub (a b : IExp ℕ) : (a - b).eval = a.eval - b.eval := rfl

/-- The value of a product. -/
@[simp] theorem IExp.eval_mul (a b : IExp ℕ) : (a * b).eval = a.eval * b.eval := rfl

/-- The value of a remainder. -/
@[simp] theorem IExp.eval_mod (a b : IExp ℕ) : (a % b).eval = a.eval % b.eval := rfl

/-! ### The store -/

/-- The store: a stack of tagged buffers of possibly uninitialised cells. -/
abbrev Store (P K : Type) := Array (P × Array (Option K))

section Store

variable {P K : Type} [DecidableEq P]

/-- Cell `i` of buffer `b` at tag `p`; `none` if the buffer does not exist, has another tag, the
index is out of bounds or the cell is uninitialised. -/
def Store.read (s : Store P K) (p : P) (b i : ℕ) : Option K :=
  match s[b]? with
  | some (q, arr) => if q = p then (arr[i]?).join else none
  | none => none

/-- Write `v` into cell `i` of buffer `b` at tag `p`; `none` if the buffer does not exist, has
another tag or the index is out of bounds. -/
def Store.write (s : Store P K) (p : P) (b i : ℕ) (v : K) : Option (Store P K) :=
  match s[b]? with
  | some (q, arr) => if q = p ∧ i < arr.size then some (s.set! b (q, arr.set! i (some v)))
      else none
  | none => none

/-- The `len` cells of buffer `b` from offset `off`. -/
def Store.readBlock (s : Store P K) (p : P) (b off len : ℕ) : Option (Array K) :=
  (List.range len).toArray.mapM fun i => s.read p b (off + i)

/-- Write `xs` into buffer `b` from offset `off`, one cell at a time. -/
def Store.writeBlock (s : Store P K) (p : P) (b off : ℕ) (xs : Array K) : Option (Store P K) :=
  (List.range xs.size).foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s

/-- The shape of a store: the tag and the length of each buffer. Two stores of the same shape
accept the same writes. -/
def Store.shape (s : Store P K) : Array (P × ℕ) := s.map fun x => (x.1, x.2.size)

/-- Read after write, at the written cell. -/
theorem Store.read_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') : s'.read p b i = some v := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    obtain ⟨rfl, hi⟩ := hq
    cases h
    have hb' : b < s.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp [Store.read, Array.set!, hb', hi]

/-- Read after write, at another cell. -/
theorem Store.read_of_write_eq_some_of_ne {s s' : Store P K} {p q : P} {b i b' i' : ℕ} {v : K}
    (h : s.write p b i v = some s') (hne : b' ≠ b ∨ i' ≠ i) : s'.read q b' i' = s.read q b' i' := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q', arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    obtain ⟨rfl, hi⟩ := hq
    cases h
    have hb' : b < s.size := (Array.getElem?_eq_some_iff.mp hb).1
    unfold Store.read
    by_cases hbb : b' = b
    · subst hbb
      have hii : i' ≠ i := hne.resolve_left (fun h => h rfl)
      have heq : s[b'] = (q', arr) := (Array.getElem?_eq_some_iff.mp hb).2
      simp [Array.set!, hb', heq, Ne.symm hii]
    · simp [Array.set!, Ne.symm hbb]

/-- A write keeps the number of buffers. -/
theorem Store.size_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') : s'.size = s.size := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    cases h
    simp [Array.set!]

/-- A write keeps the shape of the store. -/
theorem Store.shape_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') : s'.shape = s.shape := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h
    split_ifs at h with hq
    cases h
    obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hb
    apply Array.ext
    · simp [Store.shape, Array.set!]
    · intro k hk₁ hk₂
      by_cases hkb : k = b
      · subst hkb
        simp [Store.shape, Array.set!, heq]
      · simp only [Store.shape, Array.set!, Array.getElem_map]
        rw [Array.getElem_setIfInBounds_ne (by simpa [Store.shape] using hk₂) (Ne.symm hkb)]

/-- A write succeeds where a read of the same cell succeeds. -/
theorem Store.exists_write_eq_some_of_read_eq_some {s : Store P K} {p : P} {b i : ℕ} {v w : K}
    (h : s.read p b i = some w) : ∃ s', s.write p b i v = some s' := by
  unfold Store.read at h
  unfold Store.write
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    have hi : i < arr.size := by
      rcases hi : arr[i]? with _ | x
      · simp [hi] at h
      · exact (Array.getElem?_eq_some_iff.mp hi).1
    exact ⟨_, if_pos ⟨hq, hi⟩⟩

/-- A read of a pushed buffer: the old buffers are unchanged. -/
theorem Store.read_push_of_lt {s : Store P K} {p q : P} {arr : Array (Option K)} {b i : ℕ}
    (hb : b < s.size) : Store.read (s.push (q, arr)) p b i = s.read p b i := by
  simp [Store.read, Array.getElem?_push, Nat.ne_of_lt hb]

/-- The writes of a block write, at indices of a list, keep every other cell. -/
private theorem Store.read_of_foldlM_write_eq_some_of_ne {s s' : Store P K} {p q : P}
    {b off b' i' : ℕ} {xs : Array K} (l : List ℕ)
    (h : l.foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s = some s')
    (hne : ∀ i ∈ l, b' ≠ b ∨ i' ≠ off + i) : s'.read q b' i' = s.read q b' i' := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    rw [h]
  | cons i l ih =>
    rw [List.foldlM_cons] at h
    change (Option.bind _ fun s => List.foldlM _ s l) = some s' at h
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
    change Option.bind xs[i]? (fun v => s.write p b (off + i) v) = some s₂ at h₂
    obtain ⟨v, -, hw⟩ := Option.bind_eq_some_iff.mp h₂
    rw [ih h₃ (fun j hj => hne j (List.mem_cons_of_mem _ hj))]
    exact Store.read_of_write_eq_some_of_ne hw (hne i List.mem_cons_self)

/-- The writes of a block write, at the indices of a list without repetition, leave entry `j` of
the block in cell `off + j`. -/
private theorem Store.read_of_foldlM_write_eq_some_of_mem {s s' : Store P K} {p : P} {b off j : ℕ}
    {xs : Array K} (l : List ℕ) (hl : l.Nodup)
    (h : l.foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s = some s') (hj : j ∈ l) :
    s'.read p b (off + j) = xs[j]? := by
  induction l generalizing s with
  | nil => simp at hj
  | cons i l ih =>
    rw [List.foldlM_cons] at h
    change (Option.bind _ fun s => List.foldlM _ s l) = some s' at h
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
    change Option.bind xs[i]? (fun v => s.write p b (off + i) v) = some s₂ at h₂
    obtain ⟨v, hv, hw⟩ := Option.bind_eq_some_iff.mp h₂
    rcases List.mem_cons.mp hj with rfl | hj'
    · have hnot : j ∉ l := (List.nodup_cons.mp hl).1
      rw [Store.read_of_foldlM_write_eq_some_of_ne l h₃ (fun i hi => Or.inr (fun he => hnot (by
        have : j = i := by omega
        exact this ▸ hi))), Store.read_of_write_eq_some hw, hv]
    · exact ih (List.nodup_cons.mp hl).2 h₃ hj'

/-- Read after a block write, inside the block. -/
theorem Store.read_of_writeBlock_eq_some_of_lt {s s' : Store P K} {p : P} {b off j : ℕ}
    {xs : Array K}
    (h : s.writeBlock p b off xs = some s') (hj : j < xs.size) :
    s'.read p b (off + j) = xs[j]? := by
  exact Store.read_of_foldlM_write_eq_some_of_mem _ List.nodup_range h (List.mem_range.mpr hj)

/-- Read after a block write, outside the block. -/
theorem Store.read_of_writeBlock_eq_some_of_ne {s s' : Store P K} {p q : P} {b off b' i' : ℕ}
    {xs : Array K}
    (h : s.writeBlock p b off xs = some s') (hne : b' ≠ b ∨ i' < off ∨ off + xs.size ≤ i') :
    s'.read q b' i' = s.read q b' i' := by
  refine Store.read_of_foldlM_write_eq_some_of_ne _ h fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rcases hne with hb | hlt | hge
  · exact Or.inl hb
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)

/-- A read that succeeds is in a buffer of the store. -/
theorem Store.lt_size_of_read_eq_some {s : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.read p b i = some v) : b < s.size := by
  unfold Store.read at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · exact (Array.getElem?_eq_some_iff.mp hb).1

/-- A write that succeeds is in a buffer of the store. -/
theorem Store.lt_size_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') : b < s.size := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · exact (Array.getElem?_eq_some_iff.mp hb).1

/-- A write succeeds where a write of another value into the same cell succeeds. -/
theorem Store.exists_write_eq_some_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ}
    {v : K} (h : s.write p b i v = some s') (w : K) : ∃ s'', s.write p b i w = some s'' := by
  unfold Store.write at h ⊢
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    exact ⟨_, if_pos hq⟩

/-- Two writes into one cell: the second overwrites the first. -/
theorem Store.write_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') (w : K) : s'.write p b i w = s.write p b i w := by
  unfold Store.write at h ⊢
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    obtain ⟨rfl, hi⟩ := hq
    cases h
    have hb' : b < s.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp [Array.set!, hb', hi]

/-- A write below the top of a pushed store is a write in the store under it. -/
theorem Store.write_push_of_lt {s : Store P K} {x : P × Array (Option K)} {p : P} {b i : ℕ}
    {v : K} (hb : b < s.size) :
    Store.write (s.push x) p b i v = (s.write p b i v).map fun s' => s'.push x := by
  unfold Store.write
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hb)]
  rcases hb' : s[b]? with _ | ⟨q, arr⟩
  · rfl
  · dsimp only
    split_ifs
    · simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.size_push,
        Option.map_some, Array.set_push, hb, Nat.lt_succ_of_lt hb,
        dite_true]
    · rfl

/-- A write into the top buffer of a pushed store. -/
theorem Store.write_push_size {s : Store P K} {p : P} {arr : Array (Option K)} {i : ℕ} {v : K}
    (hi : i < arr.size) :
    Store.write (s.push (p, arr)) p s.size i v = some (s.push (p, arr.set! i (some v))) := by
  simp [Store.write, hi, Array.setIfInBounds_def, Array.set_push]

/-- A read of the top buffer of a pushed store. -/
theorem Store.read_push_size {s : Store P K} {p q : P} {arr : Array (Option K)} {i : ℕ} :
    Store.read (s.push (q, arr)) p s.size i = if q = p then (arr[i]?).join else none := by
  simp [Store.read]

/-- A write keeps the number of buffers: the writes of a fold. -/
theorem Store.size_of_foldlM_write_eq_some {s s' : Store P K} {p : P} {b : ℕ} (l : List ℕ)
    (idx : ℕ → ℕ) (f : ℕ → K) (h : l.foldlM (fun s j => s.write p b (idx j) (f j)) s = some s') :
    s'.size = s.size := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    rw [h]
  | cons i l ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
    rw [ih h₃, Store.size_of_write_eq_some h₂]

/-- The writes of a fold keep every cell they do not write. -/
theorem Store.read_of_foldlM_write_eq_some_of_forall_ne {s s' : Store P K} {p q : P}
    {b b' i' : ℕ} (l : List ℕ) (idx : ℕ → ℕ) (f : ℕ → K)
    (h : l.foldlM (fun s j => s.write p b (idx j) (f j)) s = some s')
    (hne : ∀ j ∈ l, b' ≠ b ∨ i' ≠ idx j) : s'.read q b' i' = s.read q b' i' := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    rw [h]
  | cons i l ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
    rw [ih h₃ (fun j hj => hne j (List.mem_cons_of_mem _ hj))]
    exact Store.read_of_write_eq_some_of_ne h₂ (hne i List.mem_cons_self)

/-- A block write of the values $f(0), \dots, f(n-1)$ is the fold of their writes. -/
theorem Store.writeBlock_map_range (s : Store P K) (p : P) (b off n : ℕ) (f : ℕ → K) :
    s.writeBlock p b off ((List.range n).toArray.map f) =
      (List.range n).foldlM (fun s j => s.write p b (off + j) (f j)) s := by
  unfold Store.writeBlock
  have hsize : ((List.range n).toArray.map f).size = n := by simp
  rw [hsize]
  have key : ∀ (l : List ℕ), (∀ j ∈ l, j < n) → ∀ s : Store P K,
      l.foldlM (fun s i => do s.write p b (off + i) (← ((List.range n).toArray.map f)[i]?)) s =
        l.foldlM (fun s j => s.write p b (off + j) (f j)) s := by
    intro l hl
    induction l with
    | nil => intro s; rfl
    | cons i l ih =>
      intro s
      have hi : i < n := hl i List.mem_cons_self
      have hxs : ((List.range n).toArray.map f)[i]? = some (f i) := by simp [hi]
      have ih' := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      rw [List.foldlM_cons, List.foldlM_cons]
      change Option.bind (Option.bind _ fun v => s.write p b (off + i) v) _ = _
      rw [hxs, Option.bind_some]
      exact congrArg _ (funext ih')
  exact key _ (fun j hj => List.mem_range.mp hj) s

end Store

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

end Exec

end NLAlib.Computation
