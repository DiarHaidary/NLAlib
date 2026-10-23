/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Subst
public import NLAlib.Computation.Exact

/-!
# The coordinate (COO) implementation of an oracle

A sparse matrix in coordinate form: a pattern of `nnz` positions $(i, j)$, unrolled into the
implementation as host data, and the values `vals`, held as read-only data of size `nnz` at a tag
and counted as constant memory (D14). `NLAlib.Computation.cooImpl` serves an oracle call column
by column: it zeroes the destination column and, for each stored entry, reads its value, multiplies
it by the source entry and adds it into the destination. Each matrix-vector product costs `nnz`
multiplications, additions and reads and $N$ literals (`NLAlib.Computation.cooCost`), with one
scratch cell. The certificate `NLAlib.Computation.implementsOracle_cooImpl` makes it a valid
substitution for the exact oracle of `NLAlib.Computation.cooMatrix` (through
`NLAlib.Computation.RunsWithin.substOracle`). The index storage of the pattern is host data and
is not counted. Design: `docs/design/Computation.md` (D4, D14).

## Main definitions

* `NLAlib.Computation.cooImpl`, `NLAlib.Computation.cooMatrix`, `NLAlib.Computation.cooInterp`,
  `NLAlib.Computation.cooCost`.

## Main results

* `NLAlib.Computation.implementsOracle_cooImpl`: the certificate.
-/

@[expose] public section

namespace NLAlib.Computation

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- **The COO implementation of an oracle call**: for each of the `cols` columns, zero the
destination column, then for each entry $e$ of the pattern at position $(i, j)$ read value $e$ of
the read-only data, multiply it by source entry $j$ and add it into destination entry $i$. One
scratch cell. The pattern is host data, unrolled into the program. -/
def cooImpl {VB VI : Type} (N : IExp VI) (pattern : List (ℕ × ℕ)) (_o : ι) (p : P) (dst : VB)
    (dOff : IExp VI) (src : VB) (sOff : IExp VI) (cols : IExp VI) : Stmt P ι VB VI :=
  Builder.run <| Builder.named "coo_apply"
      [.idx N, .buf dst, .idx dOff, .buf src, .idx sOff, .idx cols] do
    let t ← Builder.alloc p 1
    Builder.forRange cols fun c => do
      Builder.forRange N fun i => Builder.ins (.lit p ⟨dst, dOff + .var i + N * .var c⟩ 0)
      pattern.zipIdx.forM fun ((i, j), e) => do
        Builder.stmt (.rom p ⟨t, 0⟩ (.const e))
        Builder.ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨src, sOff + .const j + N * .var c⟩)
        Builder.ins (.bin p .add ⟨dst, dOff + .const i + N * .var c⟩
          ⟨dst, dOff + .const i + N * .var c⟩ ⟨t, 0⟩)

/-- The $N \times N$ matrix of a pattern and values: entry $(i, j)$ is the sum of the values of
the pattern entries at position $(i, j)$ (repeated positions add up). -/
def cooMatrix {N : ℕ} (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun i j => ∑ e ∈ Finset.range pattern.length,
    if pattern[e]? = some (i.1, j.1) then vals e else 0

/-- The interpretation with the COO values as read-only data of size `nnz` at tag `p₀`, the
oracle the exact one of `NLAlib.Computation.cooMatrix`. -/
noncomputable def cooInterp {N : ℕ} (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜)
    (ξ : Dist → ℕ → ℝ) (p₀ : P) : Interp P ι 𝕜 (OpCount P ι) :=
  { exactInterp (fun _ => cooMatrix (N := N) pattern vals) ξ with
    rom := fun e => if e < pattern.length then some (vals e) else none
    romSize := fun q => if q = p₀ then pattern.length else 0 }

/-- The cost of the COO implementation: a matrix-vector product at tag $p$ is `nnz`
multiplications, additions and read-only reads and $N$ literals at $p$; a load costs nothing. -/
noncomputable def cooCost (N nnz : ℕ) : OpKind P ι → OpCount P ι
  | .matvec p _ => Finsupp.single (.bin p .mul) nnz + Finsupp.single (.bin p .add) nnz +
      Finsupp.single (.rom p) nnz + Finsupp.single (.lit p) N
  | _ => 0

/-! ### Store lemmas (private; to move to `Exec.lean` in the closing step) -/

namespace Sparse

section StoreLemmas

variable {K : Type}

omit [DecidableEq P] in
private theorem shape_getElem? {s : Store P K} {b : ℕ} :
    s.shape[b]? = s[b]?.map fun x => (x.1, x.2.size) := by
  simp [Store.shape]

/-- A write at tag `p` keeps every read at another tag. -/
private theorem read_of_write_of_ne_tag {s s' : Store P K} {p q : P} {b i b' i' : ℕ} {v : K}
    (h : s.write p b i v = some s') (hq : q ≠ p) : s'.read q b' i' = s.read q b' i' := by
  by_cases hc : b' = b ∧ i' = i
  · obtain ⟨rfl, rfl⟩ := hc
    unfold Store.write at h
    rcases hb : s[b']? with _ | ⟨r, arr⟩ <;> rw [hb] at h
    · exact absurd h (by simp)
    · dsimp only at h
      split_ifs at h with hr
      obtain ⟨rfl, hi⟩ := hr
      cases h
      obtain ⟨hb', heq⟩ := Array.getElem?_eq_some_iff.mp hb
      simp [Store.read, Array.set!, hb', heq, Ne.symm hq]
  · exact Store.read_of_write_eq_some_of_ne h (by tauto)

/-- A write succeeds at a cell the shape provides. -/
private theorem exists_write_of_shape {s : Store P K} {p : P} {b i n : ℕ} (v : K)
    (hs : s.shape[b]? = some (p, n)) (hi : i < n) : ∃ s', s.write p b i v = some s' := by
  rw [shape_getElem?] at hs
  unfold Store.write
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at hs
  · simp at hs
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨_, if_pos ⟨rfl, hi⟩⟩

/-- A successful read gives the shape of its buffer. -/
private theorem shape_of_read_eq_some {s : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.read p b i = some v) : ∃ n, s.shape[b]? = some (p, n) ∧ i < n := by
  unfold Store.read at h
  rw [shape_getElem?]
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · simp at h
  · dsimp only at h
    split_ifs at h with hq
    subst hq
    refine ⟨arr.size, rfl, ?_⟩
    rcases hi : arr[i]? with _ | x
    · simp [hi] at h
    · exact (Array.getElem?_eq_some_iff.mp hi).1

/-- A read at a tag other than the buffer's fails. -/
private theorem read_eq_none_of_shape {s : Store P K} {p q : P} {b i n : ℕ}
    (hs : s.shape[b]? = some (p, n)) (hq : q ≠ p) : s.read q b i = none := by
  rw [shape_getElem?] at hs
  unfold Store.read
  rcases hb : s[b]? with _ | ⟨r, arr⟩
  · rfl
  · rw [hb] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    simp [Ne.symm hq]

/-- Stores of one shape with the same reads are equal. -/
private theorem Store.ext_of_shape {s s' : Store P K} (hs : s.shape = s'.shape)
    (hr : ∀ q b i, s.read q b i = s'.read q b i) : s = s' := by
  have hsize : s.size = s'.size := by simpa [Store.shape] using congrArg Array.size hs
  refine Array.ext hsize fun b h₁ h₂ => ?_
  have hb := congrArg (·[b]?) hs
  simp only [shape_getElem?, Array.getElem?_eq_getElem h₁, Array.getElem?_eq_getElem h₂,
    Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨hq, hn⟩ := hb
  refine Prod.ext hq (Array.ext hn fun i hi₁ hi₂ => ?_)
  have := hr s[b].1 b i
  simp only [Store.read, Array.getElem?_eq_getElem h₁, Array.getElem?_eq_getElem h₂, ← hq,
    if_true, Array.getElem?_eq_getElem hi₁, Array.getElem?_eq_getElem hi₂, Option.join_some]
    at this
  exact this

/-- Writes at the indices of a list keep the shape. -/
private theorem shape_of_foldlM_write {s s' : Store P K} {p : P} {b off : ℕ} {xs : Array K}
    (l : List ℕ) (h : l.foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s = some s') :
    s'.shape = s.shape := by
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
    rw [ih h₃, Store.shape_of_write_eq_some hw]

/-- A block write keeps the shape. -/
private theorem shape_of_writeBlock {s s' : Store P K} {p : P} {b off : ℕ} {xs : Array K}
    (h : s.writeBlock p b off xs = some s') : s'.shape = s.shape :=
  shape_of_foldlM_write _ h

private theorem mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys →
      ys.length = l.length ∧ ∀ k (hk : k < l.length) (hk' : k < ys.length), f l[k] = some ys[k]
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | a :: l, ys, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨hlen, hk⟩ := mapM_eq_some hbs
    refine ⟨by simp [hlen], fun k hk₁ hk₂ => ?_⟩
    rcases k with _ | k
    · simpa using hb
    · simpa using hk k (by simpa using hk₁) (by simpa using hk₂)

/-- A block read reads each cell of the block. -/
private theorem read_of_readBlock {s : Store P K} {p : P} {b off len : ℕ} {X : Array K}
    (h : s.readBlock p b off len = some X) :
    X.size = len ∧ ∀ m < len, s.read p b (off + m) = X[m]? := by
  unfold Store.readBlock at h
  rw [List.mapM_toArray] at h
  obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hlen, hk⟩ := mapM_eq_some hys
  refine ⟨by simpa using hlen, fun m hm => ?_⟩
  have hm' : m < ys.length := by simpa [hlen] using hm
  have := hk m (by simpa using hm) hm'
  simp only [List.getElem_range] at this
  rw [this]
  simp [List.getElem?_eq_getElem hm']

/-- A read past the last buffer fails. -/
private theorem read_eq_none_of_size_le {s : Store P K} {q : P} {b i : ℕ} (hb : s.size ≤ b) :
    s.read q b i = none := by
  simp [Store.read, Array.getElem?_eq_none hb]

/-- Popping the last buffer keeps the reads of the others. -/
private theorem read_pop_of_lt {s : Store P K} {q : P} {b i : ℕ} (hb : b < s.size - 1) :
    Store.read (Array.pop s) q b i = s.read q b i := by
  have hb' : b < s.size := by omega
  simp [Store.read, hb, Array.getElem?_eq_getElem hb']

omit [DecidableEq P] in
private theorem shape_pop (s : Store P K) : Store.shape (Array.pop s) = s.shape.pop := by
  simp [Store.shape]

omit [DecidableEq P] in
private theorem size_shape (s : Store P K) : s.shape.size = s.size := by
  simp [Store.shape]

/-- The buffers of a successful oracle call exist in the store, and the destination block fits in
its buffer, also after a scratch buffer is pushed. -/
private theorem callFacts {s s₁ : Store P K} {p : P} {dst src dOff sOff L : ℕ} {X Y : Array K}
    (arr : Array (Option K)) (hX : s.readBlock p src sOff L = some X)
    (hs₁ : s.writeBlock p dst dOff Y = some s₁) (hYs : Y.size = L) :
    (0 < L → src < s.size) ∧ (0 < L → dst < s.size) ∧
      ∀ m < L, ∃ n, (Store.shape (s.push (p, arr)))[dst]? = some (p, n) ∧ dOff + m < n := by
  obtain ⟨hXs, hXr⟩ := read_of_readBlock hX
  have hdst₀ : ∀ m < L, ∃ n, s.shape[dst]? = some (p, n) ∧ dOff + m < n := by
    intro m hm
    obtain ⟨n, hn, hlt⟩ := shape_of_read_eq_some
      ((Store.read_of_writeBlock_eq_some_of_lt (j := m) hs₁ (by omega)).trans
        (Array.getElem?_eq_getElem (by omega)))
    exact ⟨n, shape_of_writeBlock hs₁ ▸ hn, hlt⟩
  have hdstlt : 0 < L → dst < s.size := fun h => by
    obtain ⟨n, hn, -⟩ := hdst₀ 0 h
    simpa [size_shape] using (Array.getElem?_eq_some_iff.mp hn).1
  refine ⟨fun h => ?_, hdstlt, fun m hm => ?_⟩
  · obtain ⟨n, hn, -⟩ := shape_of_read_eq_some ((hXr 0 h).trans
      (Array.getElem?_eq_getElem (by omega)))
    simpa [size_shape] using (Array.getElem?_eq_some_iff.mp hn).1
  · obtain ⟨n, hn, hlt⟩ := hdst₀ m hm
    refine ⟨n, ?_, hlt⟩
    simpa [Store.shape, Array.getElem?_push, Nat.ne_of_lt (hdstlt (by omega))] using hn

omit [DecidableEq P] in
/-- The shape of a pushed scratch buffer. -/
private theorem shape_push_size (s : Store P K) (p : P) (n : ℕ) :
    (Store.shape (s.push (p, Array.replicate n none)))[s.size]? = some (p, n) := by
  simp only [Store.shape, Array.map_push, Array.getElem?_push, Array.size_map, if_true]
  simp

end StoreLemmas

/-! ### Folds, the frame invariant and the steps of the run -/

section Run

/-- An invariant carried along a fold over `List.range n`. -/
private theorem foldlM_range_inv {α : Type} (f : α → ℕ → Option α) (Inv : ℕ → α → Prop)
    (n : ℕ) (h : ∀ i < n, ∀ a, Inv i a → ∃ b, f a i = some b ∧ Inv (i + 1) b) (a : α)
    (ha : Inv 0 a) : ∃ b, (List.range n).foldlM f a = some b ∧ Inv n b := by
  induction n with
  | zero => exact ⟨a, rfl, ha⟩
  | succ n ih =>
    obtain ⟨b, hb, hInv⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨c, hc, hInv'⟩ := h n (by omega) b hInv
    refine ⟨c, ?_, hInv'⟩
    rw [List.range_succ, List.foldlM_append, hb]
    simpa using hc

omit [RCLike 𝕜]

/-- The frame invariant of an oracle call writing the block of `L` cells of `dst` from `dOff` at
tag `p`, with a scratch buffer `T`: the shape is that of `s₀`, every cell outside the block and
the scratch buffer reads as in `s₀`, and cell `dOff + m` of the block reads `g m`. -/
private def DInv (s₀ : Store P 𝕜) (p : P) (T dst dOff L : ℕ) (s : Store P 𝕜)
    (g : ℕ → Option 𝕜) : Prop :=
  s.shape = s₀.shape ∧
    (∀ q b i, b ≠ T → ¬(q = p ∧ b = dst ∧ dOff ≤ i ∧ i < dOff + L) →
      s.read q b i = s₀.read q b i) ∧
    ∀ m < L, s.read p dst (dOff + m) = g m

variable {s₀ s s' : Store P 𝕜} {p : P} {T dst dOff L : ℕ} {g : ℕ → Option 𝕜}

private theorem DInv.write_dst (h : DInv s₀ p T dst dOff L s g) {m : ℕ} {v : 𝕜} (hm : m < L)
    (hw : s.write p dst (dOff + m) v = some s') :
    DInv s₀ p T dst dOff L s' (Function.update g m (some v)) := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  refine ⟨(Store.shape_of_write_eq_some hw).trans hsh, fun q b i hbT hout => ?_, fun m' hm' => ?_⟩
  · rw [← hfr q b i hbT hout]
    by_cases hq : q = p
    · subst hq
      refine Store.read_of_write_eq_some_of_ne hw ?_
      by_cases hb : b = dst
      · subst hb
        exact Or.inr fun he => hout ⟨rfl, rfl, by omega, by omega⟩
      · exact Or.inl hb
    · exact read_of_write_of_ne_tag hw hq
  · by_cases hmm : m' = m
    · subst hmm
      rw [Function.update_self]
      exact Store.read_of_write_eq_some hw
    · rw [Function.update_of_ne hmm, ← hblk m' hm']
      exact Store.read_of_write_eq_some_of_ne hw (Or.inr (by omega))

private theorem DInv.write_scratch (h : DInv s₀ p T dst dOff L s g) {v : 𝕜} (hdT : dst ≠ T)
    (hw : s.write p T 0 v = some s') : DInv s₀ p T dst dOff L s' g := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  refine ⟨(Store.shape_of_write_eq_some hw).trans hsh, fun q b i hbT hout => ?_, fun m hm => ?_⟩
  · by_cases hq : q = p
    · subst hq
      rw [Store.read_of_write_eq_some_of_ne hw (Or.inl hbT), hfr _ b i hbT hout]
    · rw [read_of_write_of_ne_tag hw hq, hfr q b i hbT hout]
  · rw [Store.read_of_write_eq_some_of_ne hw (Or.inl hdT), hblk m hm]

private theorem DInv.exists_write (h : DInv s₀ p T dst dOff L s g) {b i n : ℕ} (v : 𝕜)
    (hs : s₀.shape[b]? = some (p, n)) (hi : i < n) : ∃ s', s.write p b i v = some s' :=
  exists_write_of_shape v (h.1 ▸ hs) hi

private theorem DInv.read_out (h : DInv s₀ p T dst dOff L s g) {q : P} {b i : ℕ} (hbT : b ≠ T)
    (hout : ¬(q = p ∧ b = dst ∧ dOff ≤ i ∧ i < dOff + L)) : s.read q b i = s₀.read q b i :=
  h.2.1 q b i hbT hout

/-- The store after the call: popping the scratch buffer from a store that satisfies the frame
invariant with the block values of `Y` gives the block write of `Y`. -/
private theorem pop_eq_of_DInv {st₀ s₁ sF : Store P 𝕜} {arr : Array (Option 𝕜)} {Y : Array 𝕜}
    (hs₁ : st₀.writeBlock p dst dOff Y = some s₁) (hYs : Y.size = L)
    (hI : DInv (st₀.push (p, arr)) p st₀.size dst dOff L sF g) (hg : ∀ m < L, g m = Y[m]?) :
    Array.pop sF = s₁ := by
  obtain ⟨hsh, hfr, hblk⟩ := hI
  have hsh₁ := shape_of_writeBlock hs₁
  have hsize : sF.size = st₀.size + 1 := by
    simpa [size_shape] using congrArg Array.size hsh
  have hsize₁ : s₁.size = st₀.size := by simpa [size_shape] using congrArg Array.size hsh₁
  have hread₁ : ∀ m < L, s₁.read p dst (dOff + m) = Y[m]? := fun m hm =>
    Store.read_of_writeBlock_eq_some_of_lt hs₁ (by omega)
  refine Store.ext_of_shape ?_ fun q b i => ?_
  · rw [shape_pop, hsh, hsh₁]
    simp [Store.shape]
  by_cases hb : b < st₀.size
  swap
  · rw [read_eq_none_of_size_le (by simp; omega), read_eq_none_of_size_le (by omega)]
  rw [read_pop_of_lt (by omega)]
  by_cases hin : b = dst ∧ dOff ≤ i ∧ i < dOff + L
  · obtain ⟨rfl, h₁, h₂⟩ := hin
    have hi : i = dOff + (i - dOff) := by omega
    obtain ⟨v, hv⟩ : ∃ v, Y[i - dOff]? = some v :=
      ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨n, hn, -⟩ := shape_of_read_eq_some ((hread₁ _ (by omega)).trans hv)
    by_cases hq : q = p
    · subst hq
      rw [hi, hblk _ (by omega), hg _ (by omega), hread₁ _ (by omega)]
    · rw [read_eq_none_of_shape hn hq, hfr q b i (by omega) (by tauto),
        Store.read_push_of_lt hb, read_eq_none_of_shape (hsh₁ ▸ hn) hq]
  · rw [hfr q b i (by omega) (by tauto), Store.read_push_of_lt hb,
      Store.read_of_writeBlock_eq_some_of_ne hs₁ (by omega)]

end Run

section Steps

variable {I : Interp P ι 𝕜 (OpCount P ι)} {s₀ : Store P 𝕜} {p : P} {T dst src N L : ℕ}
  {dOff sOff : IExp ℕ}

/-- One stored entry $(i, j)$ with value $a$: multiply it by source entry $j$, add into
destination entry $i$, then run `t`. -/
private theorem exec_cooStep (hsem : I.sem = exactSem) (hc : ∀ k, I.charge k = .single k 1)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {i j c e : ℕ} {a x w : 𝕜}
    (t : Stmt P ι ℕ ℕ)
    (h : DInv s₀ p T dst dOff.eval L σ.store g) (hT : s₀.shape[T]? = some (p, 1))
    (hdT : dst ≠ T) (hsT : src ≠ T) (hm : i + N * c < L)
    (hdst : ∃ n, s₀.shape[dst]? = some (p, n) ∧ dOff.eval + (i + N * c) < n)
    (hrom : I.rom e = some a) (hx : s₀.read p src (sOff.eval + j + N * c) = some x)
    (hsrc : ¬(src = dst ∧ dOff.eval ≤ sOff.eval + j + N * c ∧
      sOff.eval + j + N * c < dOff.eval + L))
    (hw : g (i + N * c) = some w) :
    ∃ s', exec I (.seq (.rom p ⟨T, .const 0⟩ (.const e))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.const j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) t)))
        σ = exec I t { σ with
          store := s', cnt := σ.cnt + (.single (.rom p) 1 + .single (.bin p .mul) 1 +
            .single (.bin p .add) 1) } ∧
      DInv s₀ p T dst dOff.eval L s' (Function.update g (i + N * c) (some (w + a * x))) := by
  obtain ⟨s₁, h₁⟩ := h.exists_write a hT one_pos
  have h₁' := h.write_scratch hdT h₁
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write (a * x) hT one_pos
  have h₂' := h₁'.write_scratch hdT h₂
  obtain ⟨n, hdsh, hdlt⟩ := hdst
  obtain ⟨s₃, h₃⟩ := h₂'.exists_write (w + a * x) hdsh hdlt
  refine ⟨s₃, ?_, h₂'.write_dst hm h₃⟩
  have rx : s₁.read p src (sOff.eval + j + N * c) = some x := by
    rw [h₁'.read_out hsT (by tauto), hx]
  have rw₂ : s₂.read p dst (dOff.eval + i + N * c) = some w := by
    rw [Nat.add_assoc, h₂'.2.2 _ hm, hw]
  rw [← Nat.add_assoc] at h₃
  simp only [exec, Instr.run, Instr.kind, IExp.eval, hrom, hsem, hc, h₁, Option.bind_some,
    Option.map_some, Store.read_of_write_eq_some h₁, rx, exactSem, h₂,
    Store.read_of_write_eq_some h₂, rw₂, h₃]
  simp only [add_assoc]

/-- The facts about a COO oracle call that every step uses. -/
private structure CooCtx (I : Interp P ι 𝕜 (OpCount P ι)) (s₀ : Store P 𝕜) (p : P)
    (T dst src N cols : ℕ) (dOff sOff : IExp ℕ) (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜)
    (x : ℕ → ℕ → 𝕜) : Prop where
  sem : I.sem = exactSem
  charge : ∀ k, I.charge k = .single k 1
  scratch : s₀.shape[T]? = some (p, 1)
  dst_ne : 0 < N * cols → dst ≠ T
  src_ne : 0 < N * cols → src ≠ T
  dst_shape : ∀ m < N * cols, ∃ n, s₀.shape[dst]? = some (p, n) ∧ dOff.eval + m < n
  rom_eq : ∀ e < pattern.length, I.rom e = some (vals e)
  src_read : ∀ c < cols, ∀ j < N, s₀.read p src (sOff.eval + j + N * c) = some (x c j)
  disj : dst ≠ src ∨ dOff.eval + N * cols ≤ sOff.eval ∨ sOff.eval + N * cols ≤ dOff.eval
  pat : ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N

/-- The contribution of pattern entry `e` to destination row `i`. -/
private def cooTerm (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜) (x : ℕ → 𝕜) (i e : ℕ) : 𝕜 :=
  match pattern[e]? with
  | some (i', j) => if i' = i then vals e * x j else 0
  | none => 0

variable {cols : ℕ} {pattern : List (ℕ × ℕ)} {vals : ℕ → 𝕜} {x : ℕ → ℕ → 𝕜}
  {G : ℕ → Option 𝕜}

omit [RCLike 𝕜] in
/-- The run of a sequence whose first part succeeds. -/
private theorem exec_seq_of_eq_some {s t : Stmt P ι ℕ ℕ} {σ σ₁ : St P 𝕜 (OpCount P ι)}
    (h : exec I s σ = some σ₁) : exec I (.seq s t) σ = exec I t σ₁ := by
  rw [exec_seq, h, Option.bind_some]

omit [RCLike 𝕜] in
/-- The run of a statement followed by `skip`. -/
private theorem exec_seq_skip (s : Stmt P ι ℕ ℕ) (σ : St P 𝕜 (OpCount P ι)) :
    exec I (.seq s .skip) σ = exec I s σ := by
  rw [exec_seq]
  cases exec I s σ <;> rfl

/-- The zero sweep: write $0$ into every destination entry of column `c`. -/
private theorem exec_cooZero (hC : CooCtx I s₀ p T dst src N cols dOff sOff pattern vals x)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {c : ℕ} (hcL : N * c + N ≤ N * cols)
    (h : DInv s₀ p T dst dOff.eval (N * cols) σ.store g) (hG : ∀ m < N * c, g m = G m) :
    ∃ σ', exec I (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + N • .single (.lit p) 1 } ∧
        DInv s₀ p T dst dOff.eval (N * cols) s' g' ∧ (∀ i < N, g' (i + N * c) = some 0) ∧
        ∀ m < N * c, g' m = G m := by
  rw [exec_loop]
  refine foldlM_range_inv _ (fun i' σ' => ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + (i' •
      .single (.lit p) 1) } ∧ DInv s₀ p T dst dOff.eval (N * cols) s' g' ∧
      (∀ i < i', g' (i + N * c) = some 0) ∧ ∀ m < N * c, g' m = G m) N ?_ σ
    ⟨σ.store, g, by simp, h, by simp, hG⟩
  rintro i' hi' σ' ⟨s, g', hσ, hI, hrow, hG'⟩
  replace hI : DInv s₀ p T dst dOff.eval (N * cols) σ'.store g' := hσ ▸ hI
  have hm : i' + N * c < N * cols := by omega
  obtain ⟨n, hdsh, hdlt⟩ := hC.dst_shape _ hm
  obtain ⟨s'', hw⟩ := hI.exists_write 0 hdsh hdlt
  refine ⟨{ σ' with store := s'', cnt := σ'.cnt + .single (.lit p) 1 }, ?_, s'', _, ?_,
    hI.write_dst hm hw, fun i hi => ?_, fun m hm' => ?_⟩
  · rw [← Nat.add_assoc] at hw
    simp only [exec, Instr.run, Instr.kind, IExp.eval, hC.sem, hC.charge, exactSem,
      Rat.cast_zero, Option.bind_some, hw, Option.map_some]
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases hii : i = i'
    · subst hii
      simp
    · rw [Function.update_of_ne (by omega)]
      exact hrow i (by omega)
  · rw [Function.update_of_ne (by omega), hG' m hm']

/-- The stored entries from position `k₀` on, unrolled. -/
private theorem exec_cooEntries (hC : CooCtx I s₀ p T dst src N cols dOff sOff pattern vals x)
    {c : ℕ} (hc : c < cols) (hcL : N * c + N ≤ N * cols)
    (F : (ℕ × ℕ) × ℕ → Builder P ι ℕ ℕ Unit)
    (hF : ∀ i j e (k : Unit → Stmt P ι ℕ ℕ), ContT.run (F ((i, j), e)) k =
      .seq (.rom p ⟨T, .const 0⟩ (.const e))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.const j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) (k ())))) :
    ∀ (l : List (ℕ × ℕ)) (k₀ : ℕ) (σ : St P 𝕜 (OpCount P ι)) (g : ℕ → Option 𝕜),
      (∀ e < l.length, pattern[k₀ + e]? = l[e]?) → k₀ + l.length = pattern.length →
      DInv s₀ p T dst dOff.eval (N * cols) σ.store g →
      (∀ i < N, g (i + N * c) =
        some (∑ e ∈ Finset.range k₀, cooTerm pattern vals (x c) i e)) →
      (∀ m < N * c, g m = G m) →
      ∃ σ', exec I (Builder.run (List.forM (l.zipIdx k₀) F)) σ = some σ' ∧
        ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + l.length • (.single (.rom p) 1 +
            .single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
          DInv s₀ p T dst dOff.eval (N * cols) s' g' ∧
          (∀ i < N, g' (i + N * c) =
            some (∑ e ∈ Finset.range pattern.length, cooTerm pattern vals (x c) i e)) ∧
          ∀ m < N * c, g' m = G m
  | [], k₀, σ, g, _, hlen, h, hg, hG => by
    simp only [List.length_nil, add_zero] at hlen
    subst hlen
    exact ⟨σ, rfl, σ.store, g, by simp, h, hg, hG⟩
  | (i, j) :: l, k₀, σ, g, hl, hlen, h, hg, hG => by
    have hk₀ : pattern[k₀]? = some (i, j) := by simpa using hl 0 (by simp)
    obtain ⟨hi, hj⟩ := hC.pat (i, j) (List.mem_of_getElem? hk₀)
    have hk₀' : k₀ < pattern.length := (List.getElem?_eq_some_iff.mp hk₀).1
    have hm : i + N * c < N * cols := by omega
    have hsrc : ¬(src = dst ∧ dOff.eval ≤ sOff.eval + j + N * c ∧
        sOff.eval + j + N * c < dOff.eval + N * cols) := by
      rcases hC.disj with h | h | h
      · exact fun h' => h h'.1.symm
      · omega
      · omega
    obtain ⟨s', hrun, hI'⟩ := exec_cooStep hC.sem hC.charge
      (Builder.run (List.forM (l.zipIdx (k₀ + 1)) F)) h hC.scratch (hC.dst_ne (by omega))
      (hC.src_ne (by omega)) hm
      (hC.dst_shape _ hm) (hC.rom_eq k₀ hk₀') (hC.src_read c hc j hj) hsrc (hg i hi)
    have hrow' : ∀ i' < N, Function.update g (i + N * c)
        (some (∑ e ∈ Finset.range k₀, cooTerm pattern vals (x c) i e + vals k₀ * x c j))
        (i' + N * c) = some (∑ e ∈ Finset.range (k₀ + 1), cooTerm pattern vals (x c) i' e) := by
      intro i' hi'
      rw [Finset.sum_range_succ]
      by_cases hii : i' = i
      · subst hii
        simp [cooTerm, hk₀]
      · rw [Function.update_of_ne (by omega), hg i' hi']
        simp [cooTerm, hk₀, Ne.symm hii]
    have hG' : ∀ m < N * c, Function.update g (i + N * c)
        (some (∑ e ∈ Finset.range k₀, cooTerm pattern vals (x c) i e + vals k₀ * x c j)) m =
          G m := fun m hm' => by
      rw [Function.update_of_ne (by omega), hG m hm']
    obtain ⟨σ'', hrun', s'', g'', hσ'', hI'', hrow'', hG''⟩ := exec_cooEntries hC hc hcL F hF l
      (k₀ + 1) { σ with store := s', cnt := σ.cnt + (.single (.rom p) 1 +
        .single (.bin p .mul) 1 + .single (.bin p .add) 1) } _ (fun e he => by
        have := hl (e + 1) (by simp; omega)
        rw [show k₀ + 1 + e = k₀ + (e + 1) by omega, this]
        simp)
      (by simp at hlen; omega) hI' hrow' hG'
    refine ⟨σ'', ?_, s'', g'', ?_, hI'', hrow'', hG''⟩
    · rw [List.zipIdx_cons]
      change exec I (ContT.run (m := Id) (F ((i, j), k₀))
        fun _ => Builder.run (List.forM (l.zipIdx (k₀ + 1)) F)) σ = _
      rw [hF, hrun, hrun']
    · rw [hσ'']
      simp only [List.length_cons, succ_nsmul', add_assoc]

/-- One column of the product: zero the destination column, then run the stored entries. -/
private theorem exec_cooCol (hC : CooCtx I s₀ p T dst src N cols dOff sOff pattern vals x)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {c : ℕ} (hc : c < cols)
    (F : (ℕ × ℕ) × ℕ → Builder P ι ℕ ℕ Unit)
    (hF : ∀ i j e (k : Unit → Stmt P ι ℕ ℕ), ContT.run (F ((i, j), e)) k =
      .seq (.rom p ⟨T, .const 0⟩ (.const e))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.const j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) (k ()))))
    (h : DInv s₀ p T dst dOff.eval (N * cols) σ.store g) (hG : ∀ m < N * c, g m = G m)
    (hY : ∀ i < N, G (i + N * c) =
      some (∑ e ∈ Finset.range pattern.length, cooTerm pattern vals (x c) i e)) :
    ∃ σ', exec I (.seq (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip)
      (Builder.run (List.forM pattern.zipIdx F))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + (N • .single (.lit p) 1 +
          pattern.length • (.single (.rom p) 1 + .single (.bin p .mul) 1 +
            .single (.bin p .add) 1)) } ∧
        DInv s₀ p T dst dOff.eval (N * cols) s' g' ∧ ∀ m < N * (c + 1), g' m = G m := by
  have hcL : N * c + N ≤ N * cols := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hc
  obtain ⟨σ₁, h₁, s₁, g₁, rfl, hI₁, hrow₁, hG₁⟩ := exec_cooZero hC hcL h hG
  rw [exec_seq_of_eq_some h₁]
  obtain ⟨σ₂, h₂, s₂, g₂, rfl, hI₂, hrow₂, hG₂⟩ := exec_cooEntries hC hc hcL F hF pattern 0
    { σ with store := s₁, cnt := σ.cnt + N • .single (.lit p) 1 } g₁
    (by simp) (by simp) hI₁ (by simpa using hrow₁) hG₁
  refine ⟨_, h₂, s₂, g₂, by simp only [add_assoc], hI₂, fun m hm => ?_⟩
  by_cases hmc : m < N * c
  · exact hG₂ m hmc
  · have hi : m - N * c < N := by rw [Nat.mul_succ] at hm; omega
    have hm' : m = (m - N * c) + N * c := by omega
    rw [hm', hrow₂ _ hi, hY _ hi]

/-- All the columns of the product. -/
private theorem exec_cooCols {colsE : IExp ℕ}
    (hC : CooCtx I s₀ p T dst src N colsE.eval dOff sOff pattern vals x)
    (F : ℕ → (ℕ × ℕ) × ℕ → Builder P ι ℕ ℕ Unit)
    (hF : ∀ c i j e (k : Unit → Stmt P ι ℕ ℕ), ContT.run (F c ((i, j), e)) k =
      .seq (.rom p ⟨T, .const 0⟩ (.const e))
        (.seq (.instr (.bin p .mul ⟨T, .const 0⟩ ⟨T, .const 0⟩
          ⟨src, .add (.add sOff (.const j)) (.mul (.const N) (.var c))⟩))
        (.seq (.instr (.bin p .add ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩
          ⟨dst, .add (.add dOff (.const i)) (.mul (.const N) (.var c))⟩ ⟨T, .const 0⟩)) (k ()))))
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜}
    (h : DInv s₀ p T dst dOff.eval (N * colsE.eval) σ.store g)
    (hY : ∀ c < colsE.eval, ∀ i < N, G (i + N * c) =
      some (∑ e ∈ Finset.range pattern.length, cooTerm pattern vals (x c) i e)) :
    ∃ σ', exec I (.loop colsE fun c => .seq (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip)
      (Builder.run (List.forM pattern.zipIdx (F c)))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + colsE.eval • (N • .single (.lit p) 1 +
          pattern.length • (.single (.rom p) 1 + .single (.bin p .mul) 1 +
            .single (.bin p .add) 1)) } ∧
        DInv s₀ p T dst dOff.eval (N * colsE.eval) s' g' ∧ ∀ m < N * colsE.eval, g' m = G m := by
  rw [exec_loop]
  refine foldlM_range_inv _ (fun c' σ' => ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt +
      c' • (N • .single (.lit p) 1 + pattern.length • (.single (.rom p) 1 +
        .single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
      DInv s₀ p T dst dOff.eval (N * colsE.eval) s' g' ∧
      ∀ m < N * c', g' m = G m) _ ?_ σ ⟨σ.store, g, by simp, h, by simp⟩
  rintro c hc σ' ⟨s, g', hσ, hI, hG'⟩
  replace hI : DInv s₀ p T dst dOff.eval (N * colsE.eval) σ'.store g' := hσ ▸ hI
  obtain ⟨σ'', hrun, s'', g'', rfl, hI', hG''⟩ :=
    exec_cooCol hC hc (F c) (hF c) hI hG' (hY c hc)
  refine ⟨_, hrun, s'', g'', ?_, hI', hG''⟩
  subst hσ
  simp only [succ_nsmul, add_assoc]

end Steps

/-- Entry $(i, c)$ of the product with the COO matrix, as the sum the run computes. -/
private theorem getElem?_flatten_cooMatrix_mul {N cols : ℕ} {pattern : List (ℕ × ℕ)}
    (hpat : ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N) (vals : ℕ → 𝕜) (X : Array 𝕜) :
    ∀ c < cols, ∀ i < N,
      (flatten (cooMatrix (N := N) pattern vals * unflatten N cols X))[i + N * c]? =
      some (∑ e ∈ Finset.range pattern.length,
        cooTerm pattern vals ((fun c j => X[j + N * c]?.getD 0) c) i e) := by
  intro c hc i hi
  rw [getElem?_flatten _ ⟨i, hi⟩ ⟨c, hc⟩, Matrix.mul_apply]
  congr 1
  simp only [cooMatrix, unflatten, Matrix.of_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold cooTerm
  rcases he : pattern[e]? with _ | ⟨i', j⟩
  · simp
  · obtain ⟨-, hj⟩ := hpat (i', j) (List.mem_of_getElem? he)
    by_cases hii : i' = i
    · subst hii
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp [Array.getD_eq_getD_getElem?]
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext (Prod.mk.inj (Option.some.inj h)).2.symm)
      · simp
    · simp [hii]

end Sparse

/-- **The COO certificate**: for a pattern with positions in $[0, N)^2$, `cooImpl` implements the
exact oracle of `cooMatrix pattern vals` under `cooInterp`, at the cost `cooCost` of each
matrix-vector product, every other kind kept, with one scratch cell and no bit scratch.
No printed source.
Result: coo-oracle-certificate -/
theorem implementsOracle_cooImpl {N : ℕ} (pattern : List (ℕ × ℕ))
    (hpat : ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N) (vals : ℕ → 𝕜) (ξ : Dist → ℕ → ℝ) (p₀ : P) :
    ImplementsOracle (exactInterp (P := P) (ι := ι) (fun _ => cooMatrix (N := N) pattern vals) ξ)
      (cooInterp (N := N) pattern vals ξ p₀)
      (fun o p dst dOff src sOff cols => cooImpl (.const N) pattern o p dst dOff src sOff cols)
      (substKind (cooCost N pattern.length)) (fun _ => 1) 0 := by
  intro o p dst dOff src sOff cols st X Y s₁ hdisj hX hY hs₁
  change dst ≠ src ∨ dOff.eval + N * cols.eval ≤ sOff.eval ∨
    sOff.eval + N * cols.eval ≤ dOff.eval at hdisj
  change st.store.readBlock p src sOff.eval (N * cols.eval) = some X at hX
  change matOracle (cooMatrix pattern vals) cols.eval X = some Y at hY
  unfold matOracle at hY
  split_ifs at hY with hXs
  cases hY
  obtain ⟨-, hXr⟩ := Sparse.read_of_readBlock hX
  set Y := flatten (cooMatrix (N := N) pattern vals * unflatten N cols.eval X) with hYdef
  have hYs : Y.size = N * cols.eval := size_flatten _
  set s₀ : Store P 𝕜 := st.store.push (p, Array.replicate (IExp.const 1).eval none) with hs₀
  obtain ⟨hsrc, hdstlt, hdst⟩ := Sparse.callFacts (Array.replicate (IExp.const 1).eval none) hX
    hs₁ hYs
  have hC : Sparse.CooCtx (cooInterp (ι := ι) (N := N) pattern vals ξ p₀) s₀ p st.store.size
      dst src N cols.eval dOff sOff pattern vals (fun c j => X[j + N * c]?.getD 0) :=
    { sem := rfl
      charge := fun _ => rfl
      scratch := Sparse.shape_push_size _ _ _
      dst_ne := fun h => Nat.ne_of_lt (hdstlt h)
      src_ne := fun h => Nat.ne_of_lt (hsrc h)
      dst_shape := hdst
      rom_eq := fun e he => if_pos he
      src_read := fun c hc j hj => by
        have hm : j + N * c < N * cols.eval := Nat.add_mul_lt_mul_of_lt_of_lt hj hc
        rw [hs₀, Store.read_push_of_lt (hsrc (by omega)), Nat.add_assoc, hXr _ hm,
          Array.getElem?_eq_getElem (by omega)]
        simp
      disj := hdisj
      pat := hpat }
  have hYc := Sparse.getElem?_flatten_cooMatrix_mul hpat vals X (cols := cols.eval)
  let F : ℕ → ℕ → (ℕ × ℕ) × ℕ → Builder P ι ℕ ℕ Unit := fun t c ((i, j), e) => do
    Builder.stmt (.rom p ⟨t, 0⟩ (.const e))
    Builder.ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨src, sOff + .const j + .const N * .var c⟩)
    Builder.ins (.bin p .add ⟨dst, dOff + .const i + .const N * .var c⟩
      ⟨dst, dOff + .const i + .const N * .var c⟩ ⟨t, 0⟩)
  have hprog : cooImpl (P := P) (ι := ι) (.const N) pattern o p dst dOff src sOff cols =
      .seq (.named "coo_apply" [.idx (.const N), .buf dst, .idx dOff, .buf src, .idx sOff,
        .idx cols] (.alloc p (.const 1) fun t => .seq (.loop cols fun c =>
      .seq (.loop (.const N) fun i => .seq (.instr (.lit p
        ⟨dst, .add (.add dOff (.var i)) (.mul (.const N) (.var c))⟩ 0)) .skip)
      (Builder.run (List.forM pattern.zipIdx (F t c)))) .skip)) .skip := rfl
  beta_reduce
  rw [hprog, Sparse.exec_seq_skip, exec_named, exec_alloc, Sparse.exec_seq_skip]
  obtain ⟨σF, hF, sF, gF, rfl, hIF, hgF⟩ := Sparse.exec_cooCols hC (F st.store.size)
    (fun _ _ _ _ _ => rfl)
    (σ := { st with
      store := s₀
      cur := Function.update st.cur p (st.cur p + (IExp.const 1).eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + (IExp.const 1).eval))
      curW := st.curW + (IExp.const 1).eval *
        (cooInterp (ι := ι) (N := N) pattern vals ξ p₀).width p
      peakW := max st.peakW (st.curW + (IExp.const 1).eval *
        (cooInterp (ι := ι) (N := N) pattern vals ξ p₀).width p) })
    ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩ hYc
  rw [hF, Option.map_some]
  refine ⟨_, rfl, Sparse.pop_eq_of_DInv hs₁ hYs hIF hgF, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · simp [cooInterp, exactInterp]
  · refine le_of_eq (congrArg (st.cnt + ·) ?_)
    simp only [substKind, cooCost, zero_add, smul_add, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    abel
  · intro q
    by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · simp [cooInterp, exactInterp]

end NLAlib.Computation
