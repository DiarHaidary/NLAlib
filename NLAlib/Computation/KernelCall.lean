/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec

/-!
# Kernel calls in the run

A kernel call `NLAlib.Computation.Stmt.kcall` runs `NLAlib.Computation.Interp.kcallStore`: it
reads its input blocks, calls a black-box kernel of the interpretation and writes the output
blocks (design note `docs/design/Computation-DynamicPrograms.md`, §4.3). This file gives the run
of a kernel call, its failure under an interpretation without that kernel, its frame (cells
outside its output blocks are unchanged), what it writes into its output blocks, and when it
succeeds. The read-back of several block writes is here, not in `NLAlib/Computation/Store.lean`,
since it is stated with `NLAlib.Computation.blockDisjoint`.

## Main results

* `NLAlib.Computation.exec_kcall`: the run of a kernel call.
* `NLAlib.Computation.Interp.kcallStore_eq_none_of_kernel_eq_none`: no kernel, no call.
* `NLAlib.Computation.Interp.read_of_kcallStore_eq_some_of_forall`: the frame of a call.
* `NLAlib.Computation.Interp.read_of_kcallStore_eq_some`: the output blocks.
* `NLAlib.Computation.Interp.exists_kcallStore_eq_some`: when a call succeeds.
* `NLAlib.Computation.Store.read_of_writeBlocks_eq_some`: reading back several disjoint block
  writes.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P]

/-- Reading back several block writes: if `s.writeBlocks p bs ys = some s'` and the blocks
`bs` are pairwise disjoint (`NLAlib.Computation.blockDisjoint`), then for every position $k$ with
block $x = (b, \mathit{off}, \ell)$ and array $y$, the array has length $\ell$ and cell
$\mathit{off} + j$ of buffer $b$ reads entry $j$ of $y$ at tag `p`, for every $j < \ell$.
No printed source. -/
theorem Store.read_of_writeBlocks_eq_some {p : P} {s s' : Store P K} {bs : List (ℕ × ℕ × ℕ)}
    {ys : List (Array K)} (h : s.writeBlocks p bs ys = some s')
    (hpw : bs.Pairwise fun x y => blockDisjoint x y = true) (k : ℕ) (x : ℕ × ℕ × ℕ)
    (y : Array K) (hx : bs[k]? = some x) (hy : ys[k]? = some y) :
    y.size = x.2.2 ∧ ∀ j < x.2.2, s'.read p x.1 (x.2.1 + j) = y[j]? := by
  induction bs generalizing s ys k with
  | nil => simp at hx
  | cons b bs ih =>
    cases ys with
    | nil => cases h
    | cons y0 ys =>
      rw [Store.writeBlocks] at h
      split_ifs at h with hsz
      obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hpb, hpw⟩ := List.pairwise_cons.mp hpw
      cases k with
      | zero =>
        cases hx
        cases hy
        refine ⟨hsz, fun j hj => ?_⟩
        rw [Store.read_of_writeBlocks_eq_some_of_forall h2 fun x' hx' => ?_,
          Store.read_of_writeBlock_eq_some_of_lt h1 (by omega)]
        have hd := hpb x' hx'
        simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hd
        omega
      | succ k => exact ih h2 hpw k hx hy

/-- The run of a kernel call: it runs `NLAlib.Computation.Interp.kcallStore` on the store at
the values of its dimensions and offsets, and charges one call of its kind at those dimensions.
No printed source. -/
theorem exec_kcall [AddMonoid C] (I : Interp P ι K C) (o : ι) (p : P) (dims : List (IExp ℕ))
    (ins outs : List (ℕ × IExp ℕ)) (st : St P K C) :
    exec I (.kcall o p dims ins outs) st =
      (I.kcallStore o p (dims.map IExp.eval) (ins.map fun x => (x.1, x.2.eval))
        (outs.map fun x => (x.1, x.2.eval)) st.store).map fun s =>
          { st with store := s, cnt := st.cnt + I.charge (.kcall p o (dims.map IExp.eval)) } := by
  rw [exec]

/-- No kernel, no call: if kernel `o` of `I` fails on every list of input blocks at the
dimensions `ds`, every call of it at `ds` fails. No printed source. -/
theorem Interp.kcallStore_eq_none_of_kernel_eq_none {I : Interp P ι K C} {o : ι} {p : P}
    {ds : List ℕ} (h : ∀ xs, I.kernel o ds xs = none) (ins outs : List (ℕ × ℕ))
    (s : Store P K) : I.kcallStore o p ds ins outs s = none := by
  unfold Interp.kcallStore
  split_ifs
  · rcases hr : s.readBlocks p (kcallBlocks ins (I.kshape o ds).1) with _ | xs
    · rfl
    · simp only [Option.bind_some, h xs, Option.bind_none]
  · rfl

/-- The frame of a kernel call: a successful call leaves every cell outside its output blocks
unchanged, at every tag: if for every output block $(b', \mathit{off}, \ell)$ of the call the cell
$(b, i)$ has $b \ne b'$, $i < \mathit{off}$ or $\mathit{off} + \ell \le i$, then it reads the same
after the call as before. No printed source. -/
theorem Interp.read_of_kcallStore_eq_some_of_forall {I : Interp P ι K C} {o : ι} {p : P}
    {ds : List ℕ} {ins outs : List (ℕ × ℕ)} {s s' : Store P K}
    (h : I.kcallStore o p ds ins outs s = some s') {q : P} {b i : ℕ}
    (hb : ∀ x ∈ kcallBlocks outs (I.kshape o ds).2, b ≠ x.1 ∨ i < x.2.1 ∨ x.2.1 + x.2.2 ≤ i) :
    s'.read q b i = s.read q b i := by
  unfold Interp.kcallStore at h
  split_ifs at h with hc
  obtain ⟨xs, -, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ys, -, h2⟩ := Option.bind_eq_some_iff.mp h1
  exact Store.read_of_writeBlocks_eq_some_of_forall h2 hb

/-- Successful block writes write one array per block. -/
private theorem length_eq_of_writeBlocks_eq_some {p : P} :
    ∀ {s s' : Store P K} {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)},
      s.writeBlocks p bs ys = some s' → bs.length = ys.length
  | _, _, [], [], _ => rfl
  | _, _, [], _ :: _, h => by cases h
  | _, _, _ :: _, [], h => by cases h
  | _, _, _ :: _, _ :: _, h => by
    rw [Store.writeBlocks] at h
    split_ifs at h
    obtain ⟨_, -, h₂⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.length_cons, length_eq_of_writeBlocks_eq_some h₂]

/-- The output blocks of a kernel call: a successful call read its input blocks, its kernel
returned one array per output block, and after the call cell $j$ of output block $k$ reads entry
$j$ of the $k$-th returned array, for every $j$ below the length of the block. The output blocks
are pairwise disjoint (the call checks it), so a later write does not overwrite an earlier one.
No printed source. -/
theorem Interp.read_of_kcallStore_eq_some {I : Interp P ι K C} {o : ι} {p : P} {ds : List ℕ}
    {ins outs : List (ℕ × ℕ)} {s s' : Store P K} (h : I.kcallStore o p ds ins outs s = some s') :
    ∃ xs ys, s.readBlocks p (kcallBlocks ins (I.kshape o ds).1) = some xs ∧
      I.kernel o ds xs = some ys ∧ ys.length = outs.length ∧
      ∀ (k : ℕ) (x : ℕ × ℕ × ℕ) (y : Array K),
        (kcallBlocks outs (I.kshape o ds).2)[k]? = some x → ys[k]? = some y →
        y.size = x.2.2 ∧ ∀ j < x.2.2, s'.read p x.1 (x.2.1 + j) = y[j]? := by
  unfold Interp.kcallStore at h
  split_ifs at h with hc
  obtain ⟨xs, hxs, h'⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ys, hys, hw⟩ := Option.bind_eq_some_iff.mp h'
  refine ⟨xs, ys, hxs, hys, ?_, Store.read_of_writeBlocks_eq_some hw hc.2.2.1⟩
  rw [← length_eq_of_writeBlocks_eq_some hw, kcallBlocks, List.length_zipWith, hc.2.1, min_self]

/-- Block writes of arrays of the block lengths succeed where every cell of every block can be
written. -/
private theorem exists_writeBlocks_eq_some {p : P} :
    ∀ {ys : List (Array K)} {bs : List (ℕ × ℕ × ℕ)} {s : Store P K},
      List.Forall₂ (fun (y : Array K) (x : ℕ × ℕ × ℕ) => y.size = x.2.2) ys bs →
      (∀ x ∈ bs, ∀ j < x.2.2, ∃ (v : K) (s' : Store P K), s.write p x.1 (x.2.1 + j) v = some s') →
      ∃ s', s.writeBlocks p bs ys = some s'
  | [], [], s, _, _ => ⟨s, rfl⟩
  | y :: _, x :: _, _, .cons hyx hF, hw => by
    obtain ⟨s₁, hs₁⟩ := Store.exists_writeBlock_eq_some_of_write (xs := y)
      fun j hj => hw x List.mem_cons_self j (hyx ▸ hj)
    obtain ⟨s', hs'⟩ := exists_writeBlocks_eq_some hF fun x' hx' j hj => by
      obtain ⟨v, _, hv⟩ := hw x' (List.mem_cons_of_mem _ hx') j hj
      exact ⟨v, Store.exists_write_eq_some_of_shape_eq (Store.shape_of_writeBlock_eq_some hs₁) hv v⟩
    exact ⟨s', by rw [Store.writeBlocks, if_pos hyx, hs₁, Option.bind_some, hs']⟩

/-- When a kernel call succeeds: if the numbers of operands are those of the shape of kernel
`o` at `ds`, the output blocks are pairwise disjoint and disjoint from the input blocks, the input
blocks read as `xs`, the kernel returns `ys` with one array of the length of each output block,
and every cell of every output block can be written at tag `p`, then the call succeeds.
No printed source. -/
theorem Interp.exists_kcallStore_eq_some {I : Interp P ι K C} {o : ι} {p : P} {ds : List ℕ}
    {ins outs : List (ℕ × ℕ)} {s : Store P K} {xs ys : List (Array K)}
    (hin : ins.length = (I.kshape o ds).1.length)
    (hout : outs.length = (I.kshape o ds).2.length)
    (hpw : (kcallBlocks outs (I.kshape o ds).2).Pairwise fun x y => blockDisjoint x y = true)
    (hio : ∀ x ∈ kcallBlocks outs (I.kshape o ds).2, ∀ y ∈ kcallBlocks ins (I.kshape o ds).1,
      blockDisjoint x y = true)
    (hxs : s.readBlocks p (kcallBlocks ins (I.kshape o ds).1) = some xs)
    (hys : I.kernel o ds xs = some ys)
    (hsize : List.Forall₂ (fun (y : Array K) (x : ℕ × ℕ × ℕ) => y.size = x.2.2) ys
      (kcallBlocks outs (I.kshape o ds).2))
    (hw : ∀ x ∈ kcallBlocks outs (I.kshape o ds).2, ∀ j < x.2.2,
      ∃ (v : K) (s'' : Store P K), s.write p x.1 (x.2.1 + j) v = some s'') :
    ∃ s', I.kcallStore o p ds ins outs s = some s' := by
  unfold Interp.kcallStore
  rw [if_pos ⟨hin, hout, hpw, hio⟩, hxs, Option.bind_some, hys, Option.bind_some]
  exact exists_writeBlocks_eq_some hsize hw

end NLAlib.Computation
