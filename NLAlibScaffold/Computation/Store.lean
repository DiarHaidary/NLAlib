/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec

/-!
# Reads after several block writes (scaffold)

Statements for `NLAlib/Computation/Store.lean` (stage COMPDYN S1a, design note
`docs/design/Computation-DynamicPrograms.md`, "S1 implementation status"): the frame of
`NLAlib.Computation.Store.writeBlocks` (a cell outside every block is unchanged) and its read-back
(a cell of block $k$ reads entry $j$ of array $k$ when the blocks are pairwise disjoint). They are
the two steps of the kernel-call lemmas of `NLAlib/Computation/Exec.lean`.

## Main results

* `NLAlib.Computation.Store.read_of_writeBlocks_eq_some_of_forall`: the frame.
* `NLAlib.Computation.Store.read_of_writeBlocks_eq_some`: the read-back.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P K : Type} [DecidableEq P]

/-- **The frame of several block writes**: if `s.writeBlocks p bs ys = some s'` and the cell
$(b, i)$ lies outside every block $(b', \mathit{off}, \ell)$ of `bs` ($b \ne b'$,
$i < \mathit{off}$ or $\mathit{off} + \ell \le i$), it reads the same after the writes as before,
at every tag. No printed source.
Proof: induction on `bs` generalizing `s` and `ys`, unfolding `Store.writeBlocks` (the cases with
lists of different lengths are `none`); in the step, `split_ifs at h` gives `y.size = b.2.2`, the
block write is `Store.read_of_writeBlock_eq_some_of_ne` (its cells are `off + j` for
`j < y.size`, all different from $(b, i)$ by the hypothesis at the head, `omega`), and the tail is
the induction hypothesis. M, about 25 lines. -/
theorem Store.read_of_writeBlocks_eq_some_of_forall {p : P} {s s' : Store P K}
    {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)} (h : s.writeBlocks p bs ys = some s')
    {q : P} {b i : ℕ} (hb : ∀ x ∈ bs, b ≠ x.1 ∨ i < x.2.1 ∨ x.2.1 + x.2.2 ≤ i) :
    s'.read q b i = s.read q b i := by
  induction bs generalizing s ys with
  | nil =>
    cases ys with
    | nil =>
      simp only [Store.writeBlocks, Option.some.injEq] at h
      rw [h]
    | cons y ys => cases h
  | cons x bs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      rw [Store.writeBlocks] at h
      split_ifs at h with hy
      obtain ⟨s₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      have hx := hb x List.mem_cons_self
      have hrest := ih h₂ (fun z hz => hb z (List.mem_cons_of_mem _ hz))
      rw [hrest]
      refine Store.read_of_writeBlock_eq_some_of_ne h₁ ?_
      rcases hx with h0 | h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by omega)
      · exact Or.inr (by omega)

/-- **Reading back several block writes**: if `s.writeBlocks p bs ys = some s'` and the blocks
`bs` are pairwise disjoint (`NLAlib.Computation.blockDisjoint`), then for every position $k$ with
block $x = (b, \mathit{off}, \ell)$ and array $y$, the array has length $\ell$ and cell
$\mathit{off} + j$ of buffer $b$ reads entry $j$ of $y$ at tag `p`, for every $j < \ell$.
No printed source.
Proof: induction on `bs` generalizing `s`, `ys` and $k$, unfolding `Store.writeBlocks`. At
$k = 0$: the head write is read back by `Store.read_of_writeBlock_eq_some_of_lt` and kept by the
tail writes by `NLAlib.Computation.Store.read_of_writeBlocks_eq_some_of_forall`, whose hypothesis is
the head's disjointness from the tail (`List.pairwise_cons`, then `blockDisjoint` unfolded by
`Bool.or_eq_true`, `decide_eq_true_eq`, `bne_iff_ne`, and `omega`). At $k + 1$: the induction
hypothesis on the tail (`List.pairwise_cons`). M, about 30 lines. -/
theorem Store.read_of_writeBlocks_eq_some {p : P} {s s' : Store P K} {bs : List (ℕ × ℕ × ℕ)}
    {ys : List (Array K)} (h : s.writeBlocks p bs ys = some s')
    (hpw : bs.Pairwise fun x y => blockDisjoint x y = true) (k : ℕ) (x : ℕ × ℕ × ℕ)
    (y : Array K) (hx : bs[k]? = some x) (hy : ys[k]? = some y) :
    y.size = x.2.2 ∧ ∀ j < x.2.2, s'.read p x.1 (x.2.1 + j) = y[j]? := by
  sorry

end NLAlib.Computation
