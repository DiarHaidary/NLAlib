/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec
public import NLAlibScaffold.Computation.Store

/-!
# Kernel calls in the run (scaffold)

Statements for `NLAlib/Computation/Exec.lean` (stage COMPDYN S1a, design note
`docs/design/Computation-DynamicPrograms.md`, §4.3 and "S1 implementation status"): the run of a
kernel call, its failure without a kernel, the frame of a kernel call (cells outside its output
blocks are unchanged), what it writes into its output blocks, and when it succeeds.

## Main results

* `NLAlib.Computation.exec_kcall`: the run of a kernel call.
* `NLAlib.Computation.Interp.kcallStore_eq_none_of_kernel_eq_none`: no kernel, no call.
* `NLAlib.Computation.Interp.read_of_kcallStore_eq_some_of_forall`: the frame of a call.
* `NLAlib.Computation.Interp.read_of_kcallStore_eq_some`: the output blocks.
* `NLAlib.Computation.Interp.exists_kcallStore_eq_some`: when a call succeeds.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P]

/-- **The run of a kernel call**: it runs `NLAlib.Computation.Interp.kcallStore` on the store at
the values of its dimensions and offsets, and charges one call of its kind at those dimensions.
No printed source.
Proof: `rw [exec]`. S, 1 line. -/
theorem exec_kcall [AddMonoid C] (I : Interp P ι K C) (o : ι) (p : P) (dims : List (IExp ℕ))
    (ins outs : List (ℕ × IExp ℕ)) (st : St P K C) :
    exec I (.kcall o p dims ins outs) st =
      (I.kcallStore o p (dims.map IExp.eval) (ins.map fun x => (x.1, x.2.eval))
        (outs.map fun x => (x.1, x.2.eval)) st.store).map fun s =>
          { st with store := s, cnt := st.cnt + I.charge (.kcall p o (dims.map IExp.eval)) } := by
  rw [exec]

/-- **No kernel, no call**: if kernel `o` of `I` fails on every list of input blocks at the
dimensions `ds`, every call of it at `ds` fails. No printed source.
Proof: `unfold Interp.kcallStore; split_ifs`; in the first branch
`Option.bind_eq_none_iff`-style: after `cases` on `s.readBlocks …`, the inner bind is the
kernel's result at `xs`, and `rw [h xs]`. S, about 5 lines. -/
theorem Interp.kcallStore_eq_none_of_kernel_eq_none {I : Interp P ι K C} {o : ι} {p : P}
    {ds : List ℕ} (h : ∀ xs, I.kernel o ds xs = none) (ins outs : List (ℕ × ℕ))
    (s : Store P K) : I.kcallStore o p ds ins outs s = none := by
  unfold Interp.kcallStore
  split_ifs
  · rcases hr : s.readBlocks p (kcallBlocks ins (I.kshape o ds).1) with _ | xs
    · rfl
    · simp only [Option.bind_some, h xs, Option.bind_none]
  · rfl

/-- **The frame of a kernel call**: a successful call leaves every cell outside its output blocks
unchanged, at every tag: if for every output block $(b', \mathit{off}, \ell)$ of the call the cell
$(b, i)$ has $b \ne b'$, $i < \mathit{off}$ or $\mathit{off} + \ell \le i$, then it reads the same
after the call as before. No printed source.
Proof: unfold `Interp.kcallStore`, peel the `if` (`split_ifs at h`) and the two binds
(`Option.bind_eq_some_iff`) to `Store.writeBlocks … = some s'`, then
`NLAlib.Computation.Store.read_of_writeBlocks_eq_some_of_forall`. S, about 6 lines. -/
theorem Interp.read_of_kcallStore_eq_some_of_forall {I : Interp P ι K C} {o : ι} {p : P}
    {ds : List ℕ} {ins outs : List (ℕ × ℕ)} {s s' : Store P K}
    (h : I.kcallStore o p ds ins outs s = some s') {q : P} {b i : ℕ}
    (hb : ∀ x ∈ kcallBlocks outs (I.kshape o ds).2, b ≠ x.1 ∨ i < x.2.1 ∨ x.2.1 + x.2.2 ≤ i) :
    s'.read q b i = s.read q b i := by
  sorry

/-- **The output blocks of a kernel call**: a successful call read its input blocks, its kernel
returned one array per output block, and after the call cell $j$ of output block $k$ reads entry
$j$ of the $k$-th returned array, for every $j$ below the length of the block. The output blocks
are pairwise disjoint (the call checks it), so a later write does not overwrite an earlier one.
No printed source.
Proof: unfold `Interp.kcallStore`; `split_ifs at h` gives the call's condition, and peel the two
binds (`Option.bind_eq_some_iff`) to the reads `xs`, the kernel's `ys` and
`Store.writeBlocks … = some s'`. The length of `ys` is that of the output blocks (`writeBlocks`
fails otherwise: induct on the blocks, or read it off `Store.writeBlocks` by cases), which is
`outs.length` by the second conjunct of the condition and `List.length_zipWith`. The last clause
is `NLAlib.Computation.Store.read_of_writeBlocks_eq_some` with the disjointness (the third
conjunct). M, about 25 lines. -/
theorem Interp.read_of_kcallStore_eq_some {I : Interp P ι K C} {o : ι} {p : P} {ds : List ℕ}
    {ins outs : List (ℕ × ℕ)} {s s' : Store P K} (h : I.kcallStore o p ds ins outs s = some s') :
    ∃ xs ys, s.readBlocks p (kcallBlocks ins (I.kshape o ds).1) = some xs ∧
      I.kernel o ds xs = some ys ∧ ys.length = outs.length ∧
      ∀ (k : ℕ) (x : ℕ × ℕ × ℕ) (y : Array K),
        (kcallBlocks outs (I.kshape o ds).2)[k]? = some x → ys[k]? = some y →
        y.size = x.2.2 ∧ ∀ j < x.2.2, s'.read p x.1 (x.2.1 + j) = y[j]? := by
  sorry

/-- **When a kernel call succeeds**: if the numbers of operands are those of the shape of kernel
`o` at `ds`, the output blocks are pairwise disjoint and disjoint from the input blocks, the input
blocks read as `xs`, the kernel returns `ys` with one array of the length of each output block,
and every cell of every output block can be written at tag `p`, then the call succeeds.
No printed source.
Proof: unfold `Interp.kcallStore`, `rw [if_pos ⟨hin, hout, hpw, hio⟩, hxs, Option.bind_some, hys,
Option.bind_some]`; then induct on `ys` and the output blocks (`List.Forall₂` induction) through
`Store.writeBlocks`: each block write succeeds by `Store.exists_writeBlock_eq_some_of_write`, and a
block write keeps the shape (`Store.shape_of_writeBlock_eq_some`), so the later cells stay writable
(`Store.exists_write_eq_some_of_shape_eq`). M, about 40 lines. -/
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
  sorry

end NLAlib.Computation
