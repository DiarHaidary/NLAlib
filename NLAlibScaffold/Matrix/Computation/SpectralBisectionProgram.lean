/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.StaticCost
public import NLAlibScaffold.Matrix.Computation.SpectralBisectionNode

/-!
# The spectral bisection program computes `eigh` (scaffold)

Statements for a new file `NLAlib/Matrix/Computation/SpectralBisectionProgram.lean` (stage COMPDYN
S2b, design note `docs/design/Computation-EighProgram.md`, §4 to §5): the refinement of the program
`NLAlib.eighProg` to the shallow `NLAlib.eigh`.

* **The recursion by levels.** The nodes of the shallow recursion at depth $d$, with their slots
  (`NLAlib.eighLoc`), have the window, tolerance and depth counter of their depth, lie in $[0, n)$,
  and have disjoint ranges; the tree of samples at the slots (`NLAlib.eighSlotTree`) restricts to
  subtrees, and the nodes `NLAlib.eighNodeAt` reaches with it are those of `NLAlib.eighLoc`.
* **The levels.** One level of the downward pass takes the arenas from holding the nodes of depth
  $d$ to holding those of depth $d + 1$ and the records of depth $d$; the spent level writes the
  junk outputs; one level of the upward pass takes the outputs of depth $d + 1$ to those of depth
  $d$ (`NLAlib.EighArenas.LevelHolds`, `NLAlib.EighArenas.RecordHolds`,
  `NLAlib.EighArenas.OutHolds`).
* **The refinement** (§7.1 of `docs/design/Computation-DynamicPrograms.md`): (a) under kernels
  that are routines on pairs, a semantics that decides flags, exact integer literals up to $n + 4$
  and the exact floor conversion, **every successful run writes exactly `NLAlib.eigh`** on the
  machine of the interpretation (`NLAlib.eighTapeMachine`) with the tree of samples at the slots;
  (b) under the standard model with every value in range, $u < 1$, $\ell_0 \ge 1$ and
  $\varepsilon, R_0 \ge 0$, **every run succeeds** (the sign step has the shallow step limit, so no
  run fails for want of steps).
* **Counts**: the static bound `NLAlib.eighCount` and the memory, and the weighted kernel bound of
  [Shah2024, Section 4] for a superadditive cost.

## Main results

* `NLAlib.eighNodeAt_eighSlotTree`, `NLAlib.eighSlotTree_append_of_eighLoc`,
  `NLAlib.eighLoc_params`, `NLAlib.eighLoc_bounds`, `NLAlib.eighLoc_disjoint`,
  `NLAlib.eighLoc_append_singleton`: the recursion by levels.
* `NLAlib.holds_of_exec_eighDownLevel`, `NLAlib.exists_exec_eighDownLevel`,
  `NLAlib.holds_of_exec_eighBottomLevel`, `NLAlib.exists_exec_eighBottomLevel`,
  `NLAlib.holds_of_exec_eighUpLevel`, `NLAlib.exists_exec_eighUpLevel`: the levels.
* `NLAlib.holds_of_exec_eighProg`, `NLAlib.exists_exec_eighProg`: the refinement for the builder.
* `NLAlib.eighProg.toStmt_compiled`, `NLAlib.eighProg.holds_of_exec_compiled`,
  `NLAlib.eighProg.exists_exec_compiled`, `NLAlib.eighProg.cnt_le_of_exec_compiled`,
  `NLAlib.eighProg.weight_le_of_exec_compiled`: the registered tree.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

/-! ### The recursion by levels -/

section Levels

variable {F : Type*} {M : FloatMachine F ℕ ℕ} {N signFuel : ℕ} {R₀ β : F}

/-- **The nodes at the slots are the nodes of the tree of samples at the slots**: at every path,
`NLAlib.eighNodeAt` with the samples `NLAlib.eighSlotTree` (from the node $x$ at slot $lo$ of depth
$d$) reaches the node that `NLAlib.eighLoc` reaches. No printed source.
Proof: induction on the path generalizing $d$, $lo$, $x$; unfold `NLAlib.eighNodeAt`,
`NLAlib.eighChild`, `NLAlib.eighLoc` and `NLAlib.eighSlotTree`: at the empty path both give $x$; at
$b :: a$ the sample at the empty path is `NLAlib.eighTapeSample N d lo` on both sides, and the
subtree of the samples below the child is the tree at the child's slot (`split` on
`NLAlib.eighStep`, the side test as in `NLAlib.eighChild`). M, about 30 lines. -/
theorem eighNodeAt_eighSlotTree :
    ∀ (a : List Bool) (d lo : ℕ) (x : EighNode F),
      eighNodeAt M N signFuel R₀ β a x (eighSlotTree M N signFuel R₀ β d lo x) =
        (eighLoc M N signFuel R₀ β d lo x a).map Prod.snd := by
  intro a
  induction a with
  | nil => intro d lo x; rfl
  | cons b a ih =>
    intro d lo x
    cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | leaf U e => simp [eighNodeAt, eighChild, eighLoc, eighSlotTree, hs]
    | shift b' A' σ =>
      by_cases hb : b = b'
      · subst hb; simp [eighNodeAt, eighChild, eighLoc, eighSlotTree, hs, ih]
      · simp [eighNodeAt, eighChild, eighLoc, eighSlotTree, hs, hb]
    | split kp h Qp Qm Ap Am σ =>
      cases b <;> simp [eighNodeAt, eighChild, eighLoc, eighSlotTree, hs, ih]

/-- **The tree of samples at the slots restricts to subtrees**: below a path that reaches the node
$y$ at slot $lo'$, the tree of samples is the tree from $y$ at slot $lo'$ of the depth of the path.
No printed source.
Proof: induction on the path generalizing $d$, $lo$, $x$, unfolding `NLAlib.eighLoc` and
`NLAlib.eighSlotTree` at $b :: a$ (`List.cons_append`); the cases of `NLAlib.eighStep` match; at a
leaf or on the absent side `h` is `none`. M, about 25 lines. -/
theorem eighSlotTree_append_of_eighLoc :
    ∀ {a : List Bool} {d lo lo' : ℕ} {x y : EighNode F},
      eighLoc M N signFuel R₀ β d lo x a = some (lo', y) →
        (fun a' => eighSlotTree M N signFuel R₀ β d lo x (a ++ a')) =
          eighSlotTree M N signFuel R₀ β (d + a.length) lo' y := by
  intro a
  induction a with
  | nil =>
    intro d lo lo' x y h
    simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    funext a'
    simp [eighSlotTree]
  | cons b a ih =>
    intro d lo lo' x y h
    funext a'
    cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | leaf U e => simp [eighLoc, hs] at h
    | shift b' A' σ =>
      by_cases hb : b = b'
      · subst hb
        simp only [eighLoc, hs, eq_self_iff_true, if_true, ite_true] at h
        have h2 := congrFun (ih h) a'
        simp only [List.cons_append, eighSlotTree, hs, List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
        exact h2
      · simp [eighLoc, hs, hb] at h
    | split kp h' Qp Qm Ap Am σ =>
      cases b
      · simp only [eighLoc, hs, Bool.false_eq_true, if_false] at h
        have h2 := congrFun (ih h) a'
        simp only [List.cons_append, eighSlotTree, hs, Bool.false_eq_true, if_false,
          List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
        exact h2
      · simp only [eighLoc, hs, if_true] at h
        have h2 := congrFun (ih h) a'
        simp only [List.cons_append, eighSlotTree, hs, if_true, List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
        exact h2

/-- **The nodes at a depth have the parameters of the depth**: a node that `NLAlib.eighLoc` reaches
from the root $(N, \mathbf{A}, R_0, \varepsilon, \ell_0)$ at a path of length $d$ has the window and
tolerance `NLAlib.eighLevelParams` at $d$ and the depth counter $\ell_0 + d$. No printed source.
Proof: induction on the path from the end (`List.reverseRecOn`) with
`NLAlib.eighLoc_append_singleton`: a child has `NLAlib.eighNextParams` of its parent's window,
tolerance and depth counter, which is `NLAlib.eighLevelParams` at $d + 1$ by definition. M, about
30 lines. -/
theorem eighLoc_params {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ} {a : List Bool}
    {lo : ℕ} {y : EighNode F}
    (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) :
    y.R = (eighLevelParams M R₀ ε ℓ₀ a.length).1 ∧ y.ε = (eighLevelParams M R₀ ε ℓ₀ a.length).2 ∧
      y.ℓ = ℓ₀ + a.length := by
  have key : ∀ (a : List Bool) (d lo : ℕ) (x y : EighNode F) (lo' : ℕ),
      x.R = (eighLevelParams M R₀ ε ℓ₀ d).1 → x.ε = (eighLevelParams M R₀ ε ℓ₀ d).2 →
      x.ℓ = ℓ₀ + d → eighLoc M N signFuel R₀ β d lo x a = some (lo', y) →
      y.R = (eighLevelParams M R₀ ε ℓ₀ (d + a.length)).1 ∧
        y.ε = (eighLevelParams M R₀ ε ℓ₀ (d + a.length)).2 ∧
        y.ℓ = ℓ₀ + (d + a.length) := by
    intro a
    induction a with
    | nil =>
      intro d lo x y lo' hR hε hℓ h
      simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [List.length_nil, Nat.add_zero]
      exact ⟨hR, hε, hℓ⟩
    | cons b a ih =>
      intro d lo x y lo' hR hε hℓ h
      have e : d + (b :: a).length = d + 1 + a.length := by simp only [List.length_cons]; omega
      have hq : eighNextParams M x.R x.ε x.ℓ = eighLevelParams M R₀ ε ℓ₀ (d + 1) := by
        rw [eighLevelParams, hR, hε, hℓ]
      cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
      | leaf U e' => simp [eighLoc, hs] at h
      | shift b' A' σ =>
        by_cases hb : b = b'
        · subst hb
          simp only [eighLoc, hs, eq_self_iff_true, if_true, ite_true] at h
          obtain ⟨h1, h2, h3⟩ := ih (d + 1) lo _ y lo'
            (by exact congrArg Prod.fst hq) (by exact congrArg Prod.snd hq)
            (by show x.ℓ + 1 = ℓ₀ + (d + 1); omega) h
          rw [e]; exact ⟨h1, h2, h3⟩
        · simp [eighLoc, hs, hb] at h
      | split kp h' Qp Qm Ap Am σ =>
        cases b
        · simp only [eighLoc, hs, Bool.false_eq_true, if_false] at h
          obtain ⟨h1, h2, h3⟩ := ih (d + 1) (lo + kp) _ y lo'
            (by exact congrArg Prod.fst hq) (by exact congrArg Prod.snd hq)
            (by show x.ℓ + 1 = ℓ₀ + (d + 1); omega) h
          rw [e]; exact ⟨h1, h2, h3⟩
        · simp only [eighLoc, hs, if_true] at h
          obtain ⟨h1, h2, h3⟩ := ih (d + 1) lo _ y lo'
            (by exact congrArg Prod.fst hq) (by exact congrArg Prod.snd hq)
            (by show x.ℓ + 1 = ℓ₀ + (d + 1); omega) h
          rw [e]; exact ⟨h1, h2, h3⟩
  obtain ⟨h1, h2, h3⟩ := key a 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ y lo rfl rfl rfl h
  rw [Nat.zero_add] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **A child's slot**: the slot and node at the path $a ++ [b]$ are those of the child on side $b$
of the node at $a$, at the slot $lo$ (one child, or the positive side of a split) or $lo + k_+$
(the negative side of a split). No printed source.
Proof: induction on $a$ generalizing $d$, $lo$, $x$; unfold `NLAlib.eighLoc` (`List.cons_append`,
`List.nil_append`). M, about 25 lines. -/
theorem eighLoc_append_singleton :
    ∀ (a : List Bool) (b : Bool) (d lo : ℕ) (x : EighNode F),
      eighLoc M N signFuel R₀ β d lo x (a ++ [b]) =
        (eighLoc M N signFuel R₀ β d lo x a).bind fun z =>
          eighLoc M N signFuel R₀ β (d + a.length) z.1 z.2 [b] := by
  intro a
  induction a with
  | nil => intro b d lo x; simp [eighLoc]
  | cons c a ih =>
    intro b d lo x
    cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | leaf U e => simp [eighLoc, hs]
    | shift b' A' σ =>
      by_cases hc : c = b'
      · subst hc
        simp only [List.cons_append, eighLoc, hs, eq_self_iff_true, if_true, ite_true, ih,
          List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
      · simp [eighLoc, hs, hc]
    | split kp h' Qp Qm Ap Am σ =>
      cases c
      · simp only [List.cons_append, eighLoc, hs, Bool.false_eq_true, if_false, ih,
          List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
      · simp only [List.cons_append, eighLoc, hs, if_true, ih, List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]

/-- **The nodes at a depth lie in $[0, N)$ and are not empty**: a node that `NLAlib.eighLoc` reaches
from a root of size $N \ge 1$ at slot $0$ has size at least $1$ and its range $[lo, lo + k)$ inside
$[0, N)$. No printed source.
Proof: induction on the path with `NLAlib.eighLoc_append_singleton`: a one-child node keeps the
size and slot; a split has $0 < k_+ < k$ (`NLAlib.eighStep`: the cases $k_+ = k$ and $k_+ = 0$ are
one-child nodes), so both children are nonempty and $[lo, lo + k_+)$, $[lo + k_+, lo + k)$ cover
$[lo, lo + k)$; `omega`. M, about 30 lines. -/
theorem eighLoc_bounds {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ} (hN : 1 ≤ N)
    {a : List Bool} {lo : ℕ} {y : EighNode F}
    (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) :
    1 ≤ y.k ∧ lo + y.k ≤ N := by
  have key : ∀ (a : List Bool) (d lo : ℕ) (x y : EighNode F) (lo' : ℕ), 1 ≤ x.k →
      lo + x.k ≤ N → eighLoc M N signFuel R₀ β d lo x a = some (lo', y) →
      1 ≤ y.k ∧ lo' + y.k ≤ N := by
    intro a
    induction a with
    | nil =>
      intro d lo x y lo' hk hN' h
      simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hk, hN'⟩
    | cons b a ih =>
      intro d lo x y lo' hk hN' h
      cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
      | leaf U e => simp [eighLoc, hs] at h
      | shift b' A' σ =>
        by_cases hb : b = b'
        · subst hb
          simp only [eighLoc, hs, eq_self_iff_true, if_true, ite_true] at h
          exact ih (d + 1) lo _ y lo' (by show 1 ≤ x.k; exact hk)
            (by show lo + x.k ≤ N; exact hN') h
        · simp [eighLoc, hs, hb] at h
      | split kp h' Qp Qm Ap Am σ =>
        have hb : 0 < kp ∧ kp < x.k := by
          unfold eighStep at hs
          dsimp only at hs
          split_ifs at hs <;> (try cases hs) <;> omega
        cases b
        · simp only [eighLoc, hs, Bool.false_eq_true, if_false] at h
          exact ih (d + 1) (lo + kp) _ y lo' (by show 1 ≤ x.k - kp; omega)
            (by show lo + kp + (x.k - kp) ≤ N; omega) h
        · simp only [eighLoc, hs, if_true] at h
          exact ih (d + 1) lo _ y lo' (by show 1 ≤ kp; omega)
            (by show lo + kp ≤ N; omega) h
  exact key a 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ y lo hN (by show 0 + N ≤ N; omega) h

/-- The slot ranges of the nodes that `NLAlib.eighLoc` reaches lie inside the range of their
start. -/
private theorem eighLoc_range_aux :
    ∀ (a : List Bool) (d lo : ℕ) (x : EighNode F) {l : ℕ} {y : EighNode F},
      eighLoc M N signFuel R₀ β d lo x a = some (l, y) → lo ≤ l ∧ l + y.k ≤ lo + x.k
  | [], d, lo, x, l, y, h => by
    simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨le_rfl, le_rfl⟩
  | b :: a, d, lo, x, l, y, h => by
    simp only [eighLoc] at h
    split at h
    · simp at h
    · rename_i b' A' σ
      split_ifs at h with hb
      · obtain ⟨h1, h2⟩ := eighLoc_range_aux a (d + 1) lo _ h
        exact ⟨h1, by simpa using h2⟩
    · rename_i kp hkp _ _ _ Ap Am _
      split_ifs at h with hb
      · obtain ⟨h1, h2⟩ := eighLoc_range_aux a (d + 1) lo _ h
        exact ⟨h1, by simp only at h2; omega⟩
      · obtain ⟨h1, h2⟩ := eighLoc_range_aux a (d + 1) (lo + kp) _ h
        exact ⟨by omega, by simp only at h2; omega⟩

/-- Two distinct paths of one length from one node reach nodes with disjoint slot ranges. -/
private theorem eighLoc_disjoint_aux :
    ∀ (a a' : List Bool) (d lo : ℕ) (x : EighNode F) (l l' : ℕ) (y y' : EighNode F),
      a.length = a'.length → a ≠ a' →
      eighLoc M N signFuel R₀ β d lo x a = some (l, y) →
      eighLoc M N signFuel R₀ β d lo x a' = some (l', y') →
      l + y.k ≤ l' ∨ l' + y'.k ≤ l
  | [], a', _, _, _, _, _, _, _, hlen, hne, _, _ => by
    cases a' with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hlen
  | b :: a, a', d, lo, x, l, l', y, y', hlen, hne, h, h' => by
    cases a' with
    | nil => simp at hlen
    | cons b' a' =>
    simp only [eighLoc] at h h'
    generalize eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) = s at h h'
    cases s with
    | leaf U dd => simp at h
    | shift c A' σ =>
      by_cases hb : b = c <;> by_cases hb' : b' = c
      · subst hb; subst hb'
        have hne' : a ≠ a' := fun e => hne (by rw [e])
        simp only [if_true] at h h'
        exact eighLoc_disjoint_aux a a' (d + 1) lo _ l l' y y' (by simpa using hlen) hne' h h'
      all_goals simp only [if_pos, if_neg, *] at h h' <;> simp at h h'
    | split kp hkp Qp Qm Ap Am σ =>
      cases b <;> cases b' <;>
        simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, ite_true,
          ite_false] at h h'
      · have hne' : a ≠ a' := fun e => hne (by rw [e])
        exact eighLoc_disjoint_aux a a' (d + 1) (lo + kp) _ l l' y y' (by simpa using hlen) hne'
          h h'
      · have h1 := eighLoc_range_aux a (d + 1) (lo + kp) _ h
        have h2 := eighLoc_range_aux a' (d + 1) lo _ h'
        dsimp only at h1 h2
        omega
      · have h1 := eighLoc_range_aux a (d + 1) lo _ h
        have h2 := eighLoc_range_aux a' (d + 1) (lo + kp) _ h'
        dsimp only at h1 h2
        omega
      · have hne' : a ≠ a' := fun e => hne (by rw [e])
        exact eighLoc_disjoint_aux a a' (d + 1) lo _ l l' y y' (by simpa using hlen) hne' h h'

/-- **The nodes at one depth have disjoint ranges**: two distinct paths of the same length that
`NLAlib.eighLoc` follows from the root reach nodes whose ranges $[lo, lo + k)$ do not meet. So the
nodes of one level partition a part of $[0, N)$, and their packed blocks in the arenas are disjoint.
No printed source.
Proof: induction on the common length with `NLAlib.eighLoc_append_singleton`: paths with distinct
parents have disjoint parent ranges (induction hypothesis) containing the children's ranges
(`NLAlib.eighLoc_bounds`' argument); siblings of a split have the disjoint ranges
$[lo, lo + k_+)$ and $[lo + k_+, lo + k)$; a one-child node has one child. M, about 40 lines. -/
theorem eighLoc_disjoint {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ}
    {a a' : List Bool} (hlen : a.length = a'.length) (hne : a ≠ a') {lo lo' : ℕ}
    {y y' : EighNode F} (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (h' : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a' = some (lo', y')) :
    lo + y.k ≤ lo' ∨ lo' + y'.k ≤ lo :=
  eighLoc_disjoint_aux a a' 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ lo lo' y y' hlen hne h h'

end Levels

/-! ### The levels -/

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! #### Helpers of `NLAlib.holds_of_exec_eighDownLevel` -/

omit [Inhabited K] in
/-- EL1: a sequence, inverted. -/
private theorem el1_seq {s t : Stmt P ι ℕ ℕ} {st st' : St P K C}
    (h : exec I (.seq s t) st = some st') : ∃ σ, exec I s st = some σ ∧ exec I t σ = some st' :=
  Option.bind_eq_some_iff.mp ((exec_seq I s t st).symm.trans h)

omit [Inhabited K] in
/-- EL1: the run of a scoped allocation, inverted. -/
private theorem el1_alloc_inv {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.seq (.alloc p len body) .skip) st = some st') :
    ∃ st₂, exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st₂ ∧
      { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p } = st' := by
  rw [exec_seq_skip, exec_alloc] at h
  exact Option.map_eq_some_iff.mp h

omit [Inhabited K] in
/-- EL1: an index literal, then the rest, inverted. -/
private theorem el1_inv_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.litIdx p dst e)) t) s = some s₂) :
    ∃ v s', I.sem.lit p (e.eval : ℚ) = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
/-- EL1: a binary operation, then the rest, inverted. -/
private theorem el1_inv_bin {p : P} {op : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.bin p op dst x y)) t) s = some s₂) :
    ∃ a c v s', s.store.read p x.buf x.idx.eval = some a ∧
      s.store.read p y.buf y.idx.eval = some c ∧ I.sem.bin p op a c = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p op) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, c, hc, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, c, v, s', ha, hc, hv, hw, h⟩

omit [Inhabited K] in
/-- EL1: a successful loop of draws into the cells $w < m$ of one buffer writes the tape values
from the current position, advances the position by $m$ and keeps the shape and every other cell. -/
private theorem el1_draw_loop {p : P} {dist : Dist} {m : IExp ℕ} {Y : ℕ} {st st' : St P K C}
    (h : exec I (.loop m fun w => (Builder.ins (ι := ι) (.draw p dist ⟨Y, .var w⟩)).run) st =
      some st') :
    st'.store.shape = st.store.shape ∧
      st'.pos = Function.update st.pos dist (st.pos dist + m.eval) ∧
      (∀ w < m.eval, st'.store.read p Y w = some (I.tape dist (st.pos dist + w))) ∧
      ∀ q b i, (b ≠ Y ∨ m.eval ≤ i) → st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = Function.update st.pos dist (st.pos dist + w) ∧
      (∀ w' < w, s.store.read p Y w' = some (I.tape dist (st.pos dist + w'))) ∧
      ∀ q b i, (b ≠ Y ∨ w ≤ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, by simp, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  change exec I (.seq (.instr (.draw p dist ⟨Y, .var w⟩)) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨s', hw', rfl⟩, rfl⟩ := hex
  simp only [IExp.eval_var] at hw'
  have hpd : s₁.pos dist = st.pos dist + w := by rw [hps]; simp
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, ?_, fun w' hw => ?_, fun q b i hb => ?_⟩
  · change Function.update s₁.pos dist (s₁.pos dist + 1) = _
    rw [hpd, hps, Function.update_idem, Nat.add_assoc]
  · change s'.read p Y w' = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega)), hrd w' h]
    · rw [Store.read_of_write_eq_some hw', hpd]
  · change s'.read q b i = _
    have hb' : b ≠ Y ∨ w ≤ i := hb.imp_right fun h => by omega
    rw [Store.read_of_write_eq_some_of_ne hw' ?_, hfr q b i hb']
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

omit [Inhabited K] in
/-- EL1: the run of a scoped index binder, inverted. -/
private theorem el1_bindIdx_inv {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st st' : St P K C}
    (h : exec I (.seq (.bindIdx p x bound body) .skip) st = some st') :
    ∃ v w, st.store.read p x.buf x.idx.eval = some w ∧ I.sem.toNat p w = some v ∧
      v ≤ bound.eval ∧
      exec I (body v) { st with cnt := st.cnt + I.charge (.toNat p) } = some st' := by
  rw [exec_seq_skip, exec_bindIdx] at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  unfold toNatStep at hr
  obtain ⟨w, hw, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hr
  split_ifs at h with hle
  exact ⟨v, w, hw, hv, hle, h⟩

omit [Inhabited K] in
/-- EL1: the run of a scoped index binder on a stored size within its bound. -/
private theorem el1_bindIdx_of_reads {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st st' : St P K C} {k : ℕ}
    (hr : ReadsIdx I.sem st.store p x.buf x.idx.eval k) (hk : k ≤ bound.eval)
    (h : exec I (.seq (.bindIdx p x bound body) .skip) st = some st') :
    exec I (body k) { st with cnt := st.cnt + I.charge (.toNat p) } = some st' := by
  obtain ⟨v, w, hw, hv, -, h⟩ := el1_bindIdx_inv h
  unfold ReadsIdx at hr
  rw [hw, Option.bind_some, hv] at hr
  obtain rfl := Option.some_inj.mp hr
  exact h

omit [Inhabited K] in
/-- EL1: a loop of no iteration. -/
private theorem el1_loop_zero {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 0) (h : exec I (.seq (.loop e b) .skip) s = some s') : s' = s := by
  rw [exec_seq_skip, exec_loop, he] at h
  simp only [List.range_zero, List.foldlM_nil] at h
  exact (Option.some_inj.mp h).symm

omit [Inhabited K] in
/-- EL1: a loop of one iteration. -/
private theorem el1_loop_one {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 1) (h : exec I (.seq (.loop e b) .skip) s = some s') :
    exec I (b 0) s = some s' := by
  rw [exec_seq_skip, exec_loop, he] at h
  simpa [List.range_one] using h

omit [Inhabited K] in
/-- EL1: a guarded block, then the rest. -/
private theorem el1_when_bind {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {st st' : St P K C}
    (h : exec I (eighWhen e b >>= f).run st = some st') :
    ∃ σ, exec I (.seq (.loop (1 - (1 - e)) fun _ => b.run) .skip) st = some σ ∧
      exec I (f ()).run σ = some st' := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl)] at h
  exact Option.bind_eq_some_iff.mp h

omit [AddMonoid C] [Inhabited K] in
/-- EL1: a size written as a literal reads back as the size. -/
private theorem el1_readsIdx {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {s : Store P K} {p : P} {b i k : ℕ} (hk : k ≤ B)
    (h : s.read p b i = I.sem.lit p ((k : ℕ) : ℚ)) : ReadsIdx I.sem s p b i k := by
  obtain ⟨z, hz, -⟩ := hlit p k hk
  unfold ReadsIdx
  rw [h, hz, Option.bind_some]
  exact hlit.toNat_eq_of_lit_eq_some htn hk hz

omit [AddMonoid C] [Inhabited K] in
/-- EL1: a read of an index transfers along equal reads. -/
private theorem el1_readsIdx_congr {sem : ScalarSem P K} {s s' : Store P K} {p : P} {b i k : ℕ}
    (he : s'.read p b i = s.read p b i) (h : ReadsIdx sem s p b i k) : ReadsIdx sem s' p b i k := by
  unfold ReadsIdx at h ⊢
  rw [he]
  exact h

omit [Inhabited K] in
/-- EL1: a held block is kept if every read of its words is kept. -/
private theorem el1_holds_keep {s s' : Store P K} {p : P} {b off l m : ℕ}
    {Y : Matrix (Fin l) (Fin m) (K × K)} (hY : pairLayout.Holds s p b off Y)
    (h : ∀ i, off ≤ i → i < off + 2 * (l * m) → s'.read p b i = s.read p b i) :
    pairLayout.Holds s' p b off Y :=
  hY.of_forall_read_eq fun i h1 h2 => h i h1 (by
    change i < off + m * l * 2 at h2
    linarith [Nat.mul_comm l m])

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: two blocks of distinct buffers are disjoint. -/
private theorem el1_bd_ne {b b' i i' l l' : ℕ} (h : b ≠ b') :
    blockDisjoint (b, i, l) (b', i', l') = true := by
  simp [blockDisjoint, h]

/-- EL1: the slots of the children of a node step at slot `lo`: none at a leaf, `lo` for one child,
`lo` and `lo + k₊` for a split. -/
private def el1_childSlot {F' : Type*} {k : ℕ} (s : EighStep F' k) (lo j : ℕ) : Prop :=
  match s with
  | .leaf _ _ => False
  | .shift _ _ _ => j = lo
  | .split kp _ _ _ _ _ _ => j = lo ∨ j = lo + kp

/-- EL1: the cells the slot `lo` of depth $d$ may write, for a node of size $k$ whose children
start at the slots `cs`. -/
private def el1_win (H : EighArenas) (n d lo k : ℕ) (cs : ℕ → Prop) (b i : ℕ) : Prop :=
  ((b = H.Qa ∨ b = H.Ua) ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
    (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
    (b = H.Ea ∧ n * d + lo ≤ i ∧ i < n * d + lo + k) ∨
    ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo) ∨
    (b = H.Sz ∧ ∃ j, lo ≤ j ∧ j < lo + k ∧ cs j ∧ i = n * (d + 1) + j)

/-- EL1: the slot `lo` of depth $d$ is done for the node $y$: its record (as
`NLAlib.EighArenas.RecordHolds`) and its children's sizes and matrices are written. -/
private def el1_done (H : EighArenas) (sem : ScalarSem P K) (s : Store P K) (p : P)
    (M : FloatMachine K ℕ ℕ) (n F d : ℕ) (R₀ β : K) (lo : ℕ) (y : EighNode K) : Prop :=
  (match eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
      | .leaf U e => ReadsIdx sem s p H.Kd (n * d + lo) 1 ∧
          pairLayout.Holds s p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
          ∀ i : Fin y.k, s.read p H.Ea (n * d + lo + i) = some (e i)
      | .shift b _ _ => ReadsIdx sem s p H.Kd (n * d + lo) (if b then 2 else 3)
      | .split kp _ Qp Qm _ _ _ => ReadsIdx sem s p H.Kd (n * d + lo) 4 ∧
          ReadsIdx sem s p H.Kp (n * d + lo) kp ∧
          pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (y.k * kp)) Qm) ∧
    ∀ (b : Bool) (lo' : ℕ) (y' : EighNode K), eighLoc M n F R₀ β d lo y [b] = some (lo', y') →
      ReadsIdx sem s p H.Sz (n * (d + 1) + lo') y'.k ∧
        pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo') y'.A

omit [AddMonoid C] [Inhabited K] in
/-- EL1: a split of a node step is proper. -/
private theorem el1_split_lt {M : FloatMachine K ℕ ℕ} {N F : ℕ} {R₀ β R ε : K} {ℓ k : ℕ}
    {A : Matrix (Fin k) (Fin k) (K × K)} {s : EighSample ℕ ℕ N} {kp : ℕ} {h : kp ≤ k}
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Ap : Matrix (Fin kp) (Fin kp) (K × K)} {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    {σ : K} (hs : eighStep M N F R₀ β A R ε ℓ s = .split kp h Qp Qm Ap Am σ) : 0 < kp ∧ kp < k := by
  unfold eighStep at hs
  dsimp only at hs
  split_ifs at hs <;> (try cases hs) <;> omega

omit [AddMonoid C] [Inhabited K] in
/-- EL1: a slot of a child is reached by a path of one step. -/
private theorem el1_childSlot_loc {M : FloatMachine K ℕ ℕ} {n F d lo j : ℕ} {R₀ β : K}
    {y : EighNode K}
    (h : el1_childSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo j) :
    ∃ (b : Bool) (y' : EighNode K), eighLoc M n F R₀ β d lo y [b] = some (j, y') := by
  revert h
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e => intro h; exact h.elim
  | shift b A' σ =>
    intro h
    change j = lo at h
    subst h
    exact ⟨b, ⟨y.k, A', (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
      y.ℓ + 1⟩, by simp [eighLoc, hs]⟩
  | split kp hkp Qp Qm Ap Am σ =>
    intro h
    change j = lo ∨ j = lo + kp at h
    rcases h with rfl | rfl
    · exact ⟨true, ⟨kp, Ap, (eighNextParams M y.R y.ε y.ℓ).1,
        (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩, by simp [eighLoc, hs]⟩
    · exact ⟨false, ⟨y.k - kp, Am, (eighNextParams M y.R y.ε y.ℓ).1,
        (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩, by simp [eighLoc, hs]⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a node window covers the cells a node step writes. -/
private theorem el1_win_buf {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (h : el1_win H n d lo k cs b i) : b ∈ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ <;> omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: the windows of slots with disjoint ranges are disjoint. -/
private theorem el1_win_disjoint {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k lo' k' : ℕ}
    {cs cs' : ℕ → Prop} {b i : ℕ} (hk' : 1 ≤ k') (hlt : lo' + k' ≤ lo)
    (h₁ : el1_win H n d lo' k' cs' b i)
    (h₂ : el1_win H n d lo k cs b i) : False := by
  have e1 : 2 * n * (lo' + k') ≤ 2 * n * lo := Nat.mul_le_mul_left _ hlt
  unfold el1_win at h₁ h₂
  rcases h₁ with ⟨rfl | rfl, h1a, h1b⟩ | ⟨rfl, h1a, h1b⟩ | ⟨rfl, h1a, h1b⟩ | ⟨rfl | rfl, h1a⟩ |
      ⟨rfl, j1, hj1a, hj1b, -, hj1⟩ <;>
    rcases h₂ with ⟨hb2 | hb2, h2a, h2b⟩ | ⟨hb2, h2a, h2b⟩ | ⟨hb2, h2a, h2b⟩ | ⟨hb2 | hb2, h2a⟩ |
      ⟨hb2, j2, hj2a, hj2b, -, hj2⟩ <;>
    first | omega | simp [EighArenas.handles, hb2] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: the window of a slot lies in the cells of depths $d$ and $d + 1$. -/
private theorem el1_win_levelCell {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hk1 : 1 ≤ k) (hk : lo + k ≤ n) (h : el1_win H n d lo k cs b i) :
    H.LevelCell n d b i ∨ H.LevelCell n (d + 1) b i := by
  have e1 : 2 * n * (lo + k) ≤ 2 * (n * n) := by
    rw [show 2 * (n * n) = 2 * n * n by ring]; exact Nat.mul_le_mul_left _ hk
  have e2 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have e3 : 2 * (n * n) * (d + 1 + 1) = 2 * (n * n) * (d + 1) + 2 * (n * n) := by ring
  have e4 : n * (d + 1) = n * d + n := by ring
  have e5 : n * (d + 1 + 1) = n * (d + 1) + n := by ring
  unfold el1_win at h
  unfold EighArenas.LevelCell
  rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1⟩ | ⟨hb, j, hj1, hj2, -, hj⟩
  · exact Or.inl (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩)
  · exact Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hb), by omega, by omega⟩))

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a cell of the size arena below depth $d + 1$ is in no window of depth $d$. -/
private theorem el1_not_win_Sz {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (hi : i < n * (d + 1)) : ¬ el1_win H n d lo k cs H.Sz i := by
  unfold el1_win
  intro h
  rcases h with ⟨hb | hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨-, j, -, -, -, hj⟩
  all_goals first | omega | simp [EighArenas.handles, hb] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a cell of the node arena below depth $d + 1$ is in no window of depth $d$. -/
private theorem el1_not_win_Ma {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (hi : i < 2 * (n * n) * (d + 1)) : ¬ el1_win H n d lo k cs H.Ma i := by
  unfold el1_win
  intro h
  rcases h with ⟨hb | hb, -⟩ | ⟨-, h1, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨hb, -⟩
  all_goals first | omega | simp [EighArenas.handles, hb] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a cell of a buffer other than seven arenas is in no window. -/
private theorem el1_not_win_buf {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hb : b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz]) : ¬ el1_win H n d lo k cs b i := by
  exact fun h => hb (el1_win_buf h)

omit [AddMonoid C] [Inhabited K] in
/-- EL1: the done facts of a slot transfer along equal reads of its window. -/
private theorem el1_done_congr {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F d : ℕ} {R₀ β : K} {lo : ℕ} {y : EighNode K} (hk1 : 1 ≤ y.k)
    (hk : lo + y.k ≤ n)
    (h : ∀ b i, el1_win H n d lo y.k
      (el1_childSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i →
        s'.read p b i = s.read p b i)
    (hd : el1_done H sem s p M n F d R₀ β lo y) : el1_done H sem s' p M n F d R₀ β lo y := by
  have hkn : y.k ≤ n := by omega
  have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ hkn
  have e1 : 2 * n * (lo + y.k) = 2 * n * lo + 2 * (n * y.k) := by ring
  obtain ⟨hr, hc⟩ := hd
  unfold el1_done
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    simp only [hs] at hr h
    obtain ⟨h1, h2, h3⟩ := hr
    refine ⟨⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)))))
      h1, el1_holds_keep h2 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inr rfl, hi1, by omega⟩),
      fun i => (h _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)))).trans (h3 i)⟩, ?_⟩
    intro b lo' y' hl
    simp [eighLoc, hs] at hl
  | shift b A' σ =>
    simp only [hs] at hr h
    refine ⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩))))) hr,
      ?_⟩
    intro b' lo' y' hl
    obtain ⟨c1, c2⟩ := hc b' lo' y' hl
    simp only [eighLoc, hs] at hl
    by_cases hb : b' = b
    swap
    · simp [hb] at hl
    simp [hb] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl,
      by omega, rfl, rfl⟩))))) c1, el1_holds_keep c2 fun i hi1 hi2 => h _ _
      (Or.inr (Or.inl ⟨rfl, hi1, by dsimp only at hi2; omega⟩))⟩
  | split kp hkp Qp Qm Ap Am σ =>
    obtain ⟨hkp0, hkpk⟩ := el1_split_lt hs
    have q1 : y.k * kp + y.k * (y.k - kp) = y.k * y.k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hkp]
    have q2 : kp * kp ≤ n * y.k := Nat.mul_le_mul (by omega) hkp
    have q3 : (y.k - kp) * (y.k - kp) ≤ n * (y.k - kp) := Nat.mul_le_mul_right _ (by omega)
    have q5 : 2 * n * (lo + kp) = 2 * n * lo + 2 * (n * kp) := by ring
    have q4 : 2 * n * (lo + kp) + 2 * (n * (y.k - kp)) = 2 * n * (lo + y.k) := by
      rw [show lo + y.k = lo + kp + (y.k - kp) by omega]; ring
    simp only [hs] at hr h
    obtain ⟨h1, h2, h3, h4⟩ := hr
    refine ⟨⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)))))
      h1, el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, rfl⟩))))) h2,
      el1_holds_keep h3 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inl rfl, hi1, by omega⟩),
      el1_holds_keep h4 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inl rfl, by omega, by omega⟩)⟩, ?_⟩
    intro b' lo' y' hl
    obtain ⟨c1, c2⟩ := hc b' lo' y' hl
    simp only [eighLoc, hs] at hl
    cases b'
    · simp at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine ⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo + kp,
        by omega, by omega, Or.inr rfl, rfl⟩))))) c1, el1_holds_keep c2 fun i hi1 hi2 => h _ _
        (Or.inr (Or.inl ⟨rfl, by omega, by dsimp only at hi2; omega⟩))⟩
    · simp at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine ⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl,
        by omega, Or.inl rfl, rfl⟩))))) c1, el1_holds_keep c2 fun i hi1 hi2 => h _ _
        (Or.inr (Or.inl ⟨rfl, hi1, by dsimp only at hi2; omega⟩))⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a size cell in a window is a child slot. -/
private theorem el1_win_Sz {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (h : el1_win H n d lo k cs H.Sz i) :
    ∃ j, cs j ∧ i = n * (d + 1) + j := by
  rcases h with ⟨hb | hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨-, j, -, -, hj, hi⟩
  all_goals first | exact ⟨j, hj, hi⟩ | (exfalso; simp [EighArenas.handles, hb] at hnd)

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: the cells outside a window of a leaf are outside its blocks. -/
private theorem el1_leaf_bd {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hk : lo + k ≤ n) (hW : ¬ el1_win H n d lo k cs b i) :
    blockDisjoint (b, i, 1) (H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)) = true ∧
      blockDisjoint (b, i, 1) (H.Ea, n * d + lo, k) = true ∧
      blockDisjoint (b, i, 1) (H.Kd, n * d + lo, 1) = true := by
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have e1 : 2 * n * (lo + k) = 2 * n * lo + 2 * (n * k) := by ring
  have h1 : ¬ ((b = H.Qa ∨ b = H.Ua) ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * d + 2 * n * (lo + k)) := fun h => hW (Or.inl h)
  have h3 : ¬ (b = H.Ea ∧ n * d + lo ≤ i ∧ i < n * d + lo + k) :=
    fun h => hW (Or.inr (Or.inr (Or.inl h)))
  have h4 : ¬ ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo) :=
    fun h => hW (Or.inr (Or.inr (Or.inr (Or.inl h))))
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩ <;> omega

omit [DecidableEq P] [Inhabited K] in
/-- EL1: the arenas stay allocated under a change of store of the same shape at the arenas. -/
private theorem el1_shaped_of_eq {H : EighArenas} {s s' : Store P K} {p : P} {n D : ℕ}
    (h : ∀ b ∈ H.handles, s'.shape[b]? = s.shape[b]?) (hH : H.Shaped s p n D) :
    H.Shaped s' p n D := by
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := hH
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := h
  exact ⟨hnd, l1.trans hMa, l2.trans hUa, l3.trans hQa, l4.trans hEa, l5.trans hSz, l6.trans hKd,
    l7.trans hKp, l8.trans hLv⟩

/-- EL1: the body of the slot loop of `NLAlib.eighDownLevel` at slot `lo`, with the scratch
buffer `t` and the constants in `c`. -/
private def el1_slotBody (p : P) (mm qr : ι)
    (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo : ℕ) : Builder P ι ℕ ℕ Unit :=
  Builder.bindIdx p ⟨Sz, eighSlotOff (.const n) (.const d) (.var lo)⟩ (.const n - .var lo)
    fun k => eighWhen (.var k) do
      eighWhen (1 - (.var k - 1))
        (eighLeafBlock p true (.var k) Ma (eighBlockOff (.const n) (.const d) (.var lo)) Ua
          (eighBlockOff (.const n) (.const d) (.var lo)) Ea
          (eighSlotOff (.const n) (.const d) (.var lo))
          ⟨Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩)
      eighWhen (.var k - 1) do
        ins (.bin p .mul ⟨t, 4⟩ ⟨Lv, 2 * .const d + 1⟩ ⟨par, 0⟩)
        ifThenElse p .le ⟨Lv, 2 * .const d⟩ ⟨t, 4⟩
          (eighLeafBlock p false (.var k) Ma (eighBlockOff (.const n) (.const d) (.var lo)) Ua
            (eighBlockOff (.const n) (.const d) (.var lo)) Ea
            (eighSlotOff (.const n) (.const d) (.var lo))
            ⟨Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩)
          (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo) (.var k)
            par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)

omit [Inhabited K] in
/-- EL1: a slot that starts no node reads the size $0$ and is skipped. -/
private theorem el1_slot_skip {p : P} {mm qr : ι}
    {n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo : ℕ} {s s' : St P K C}
    (hSz : ReadsIdx I.sem s.store p Sz (n * d + lo) 0)
    (h : exec I (el1_slotBody p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo).run s =
      some s') :
    s'.store = s.store ∧ s'.pos = s.pos := by
  unfold el1_slotBody at h
  have h := el1_bindIdx_of_reads (k := 0) (by exact hSz) (Nat.zero_le _) h
  have e := el1_loop_zero (by change 1 - (1 - 0) = 0; omega) h
  subst e
  exact ⟨rfl, rfl⟩

/-- EL1: two builders run the same under continuations that run the same (used to move index
variables to constants inside a block, piece by piece). -/
private def el1_Equiv (I : Interp P ι K C) (X Y : Builder P ι ℕ ℕ Unit) : Prop :=
  ∀ k k' : Unit → Stmt P ι ℕ ℕ, (∀ st, exec I (k ()) st = exec I (k' ()) st) →
    ∀ st, exec I (ContT.run X k) st = exec I (ContT.run Y k') st

omit [Inhabited K] in
private theorem el1E_stmt {S S' : Stmt P ι ℕ ℕ} (h : ∀ st, exec I S st = exec I S' st) :
    el1_Equiv I (Builder.stmt S) (Builder.stmt S') := by
  intro k k' hk st
  change exec I (.seq S (k ())) st = exec I (.seq S' (k' ())) st
  rw [exec_seq, exec_seq, h st]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
private theorem el1E_ins {i i' : Instr P ℕ ℕ} (h : i.normIdx = i'.normIdx) :
    el1_Equiv I (Builder.ins i) (Builder.ins i') :=
  el1E_stmt fun st => exec_eq_of_normIdx_eq I (by simp only [Stmt.normIdx, h]) st

omit [Inhabited K] in
private theorem el1E_kcall {o : ι} {p : P} {dims dims' : List (IExp ℕ)}
    {ins ins' outs outs' : List (ℕ × IExp ℕ)}
    (h : (Stmt.kcall o p dims ins outs).normIdx = (Stmt.kcall o p dims' ins' outs').normIdx) :
    el1_Equiv I (Builder.stmt (.kcall o p dims ins outs))
      (Builder.stmt (.kcall o p dims' ins' outs')) :=
  el1E_stmt fun st => exec_eq_of_normIdx_eq I h st

omit [Inhabited K] in
private theorem el1E_pure : el1_Equiv I (pure () : Builder P ι ℕ ℕ Unit) (pure ()) :=
  fun _ _ hk st => hk st

omit [Inhabited K] in
private theorem el1E_bind {a a' : Builder P ι ℕ ℕ Unit} {f f' : Unit → Builder P ι ℕ ℕ Unit}
    (ha : el1_Equiv I a a') (hf : el1_Equiv I (f ()) (f' ())) :
    el1_Equiv I (a >>= f) (a' >>= f') := fun k k' hk st =>
  ha (fun u => ContT.run (f u) k) (fun u => ContT.run (f' u) k') (fun st => hf k k' hk st) st

omit [Inhabited K] in
private theorem el1E_allocBind {p : P} {len len' : IExp ℕ} {f f' : ℕ → Builder P ι ℕ ℕ Unit}
    (hl : len.eval = len'.eval) (hf : ∀ h, el1_Equiv I (f h) (f' h)) :
    el1_Equiv I (Builder.alloc p len >>= f) (Builder.alloc p len' >>= f') := by
  intro k k' hk st
  change exec I (.alloc p len fun h => ContT.run (f h) k) st =
    exec I (.alloc p len' fun h => ContT.run (f' h) k') st
  rw [exec_alloc, exec_alloc, hl, hf _ k k' hk]

omit [Inhabited K] in
private theorem el1E_scope {b b' : Builder P ι ℕ ℕ Unit} (hb : el1_Equiv I b b') :
    el1_Equiv I (Builder.scope b) (Builder.scope b') := by
  intro k k' hk st
  change exec I (.seq b.run (k ())) st = exec I (.seq b'.run (k' ())) st
  rw [exec_seq, exec_seq,
    show exec I b.run st = exec I b'.run st from hb (fun _ => .skip) (fun _ => .skip)
      (fun _ => rfl) st]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
private theorem el1E_forRange {n n' : IExp ℕ} {body body' : ℕ → Builder P ι ℕ ℕ Unit}
    (hn : n.eval = n'.eval) (hb : ∀ i, el1_Equiv I (body i) (body' i)) :
    el1_Equiv I (Builder.forRange n body) (Builder.forRange n' body') := by
  apply el1E_stmt
  intro st
  rw [exec_loop, exec_loop, hn]
  congr 1
  funext s i
  exact hb i _ _ (fun _ => rfl) s

omit [Inhabited K] in
private theorem el1E_bindIdx {p : P} {x x' : Cell ℕ ℕ} {bound bound' : IExp ℕ}
    {body body' : ℕ → Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx)
    (hb : bound.eval = bound'.eval) (h : ∀ i, el1_Equiv I (body i) (body' i)) :
    el1_Equiv I (Builder.bindIdx p x bound body) (Builder.bindIdx p x' bound' body') := by
  apply el1E_stmt
  intro st
  have e1 : toNatStep I p x st = toNatStep I p x' st := by
    rw [show toNatStep I p x st = toNatStep I p x.normIdx st from rfl, hx]
    rfl
  rw [exec_bindIdx, exec_bindIdx, e1, hb]
  congr 1
  funext r
  split_ifs
  · exact h _ _ _ (fun _ => rfl) _
  · rfl

omit [Inhabited K] in
private theorem el1E_ite {p : P} {c : CmpOp} {x y x' y' : Cell ℕ ℕ}
    {t e t' e' : Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx) (hy : y.normIdx = y'.normIdx)
    (ht : el1_Equiv I t t') (he : el1_Equiv I e e') :
    el1_Equiv I (Builder.ifThenElse p c x y t e) (Builder.ifThenElse p c x' y' t' e') := by
  apply el1E_stmt
  intro st
  have e1 : cmpStep I p c x y st = cmpStep I p c x' y' st := by
    rw [show cmpStep I p c x y st = cmpStep I p c x.normIdx y.normIdx st from rfl, hx, hy]
    rfl
  rw [exec_ite, exec_ite, e1]
  congr 1
  funext r
  split
  · exact ht _ _ (fun _ => rfl) _
  · exact he _ _ (fun _ => rfl) _

omit [Inhabited K] in
private theorem el1E_named {nm nm' : String} {args args' : List (Arg ℕ ℕ)}
    {b b' : Builder P ι ℕ ℕ Unit} (h : el1_Equiv I b b') :
    el1_Equiv I (Builder.named nm args b) (Builder.named nm' args' b') := by
  apply el1E_stmt
  intro st
  rw [exec_named, exec_named]
  exact h _ _ (fun _ => rfl) st

set_option maxHeartbeats 4000000 in
-- The walk goes through every statement of the node step.
omit [Inhabited K] in
/-- EL1: the node step at index variables runs as at the constants of their values. -/
private theorem el1_node_equiv (p : P) (mm qr : ι) (n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp
    c : ℕ) :
    el1_Equiv I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo)
      (.var k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
    (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) := by
  unfold eighNodeBlock
  repeat' first
    | rfl
    | exact el1E_pure
    | apply el1E_ins
    | apply el1E_kcall
    | apply el1E_forRange
    | apply el1E_bindIdx
    | apply el1E_ite
    | apply el1E_named
    | apply el1E_scope
    | apply el1E_allocBind
    | apply el1E_bind
    | intro _

omit [Inhabited K] in
/-- EL1: the node step at index variables runs as at the constants of their values. -/
private theorem el1_node_congr (p : P) (mm qr : ι) (n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp
    c : ℕ) (st : St P K C) :
    exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo) (.var k)
      par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
    exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st :=
  el1_node_equiv p mm qr n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp c (fun _ => .skip)
    (fun _ => .skip) (fun _ => rfl) st

omit [Inhabited K] in
/-- EL1: a leaf at an index variable runs as at the constant of its value. -/
private theorem el1_leaf_congr (p : P) (diag : Bool) (k Ma Ua Ea : ℕ) (mo uo eo : IExp ℕ)
    (kd : Cell ℕ ℕ) (st : St P K C) :
    exec I (eighLeafBlock (ι := ι) p diag (.var k) Ma mo Ua uo Ea eo kd).run st =
      exec I (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd).run st := by
  have hE : el1_Equiv I (eighLeafBlock (ι := ι) p diag (.var k) Ma mo Ua uo Ea eo kd)
      (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd) := by
    cases diag <;> unfold eighLeafBlock <;>
    repeat' first
      | rfl
      | exact el1E_pure
      | apply el1E_ins
      | apply el1E_kcall
      | apply el1E_forRange
      | apply el1E_bindIdx
      | apply el1E_ite
      | apply el1E_named
      | apply el1E_scope
      | apply el1E_allocBind
      | apply el1E_bind
      | intro _
  exact hE (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

set_option maxHeartbeats 1600000 in
-- The slot unfolds the binder, two guards, the window test and the node step.
/-- EL1: the slot of a node of depth $d$: its record and its children are written, and every cell
outside its window and the scratch cell `t[4]` is kept. -/
private theorem el1_slot_node {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P)
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hd : d < D)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c t lo : ℕ} {s s' : St P K C} {R₀ β : K} {y : EighNode K} (hk1 : 1 ≤ y.k)
    (hkn : lo + y.k ≤ n) (hℓ : y.ℓ = ℓ₀ + d) (hH : H.Shaped s.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (ht : t ∉ H.handles ++ [par, c])
    (hSz : ReadsIdx I.sem s.store p H.Sz (n * d + lo) y.k)
    (hA : pairLayout.Holds s.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A)
    (hR : s.store.read p H.Lv (2 * d) = some y.R)
    (hε : s.store.read p H.Lv (2 * d + 1) = some y.ε)
    (hpar : s.store.read p par 0 = some R₀ ∧ s.store.read p par 2 = some β)
    (hSu : 2 ≤ y.k → s.store.read p Su lo = some (I.tape .uniform (n * d + lo)) ∧
      (Su = t → lo ≠ 4))
    (hSg : 2 ≤ y.k → (∀ w < 4 * (n * n),
      s.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) ∧ Sg ≠ t)
    (hc : s.store.read p c 0 = I.sem.lit p 1 ∧ s.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      s.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      s.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      s.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (el1_slotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c t lo).run s = some s') :
    el1_done H I.sem s'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β lo y ∧
      (∀ q b i, ¬ el1_win H n d lo y.k (el1_childSlot (eighStep (eighTapeMachine I p mmR qrR) n F
          R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i → ¬ (b = t ∧ i = 4) →
        s'.store.read q b i = s.store.read q b i) ∧
      s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
  have dUaMa : H.Ua ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dEaMa : H.Ea ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dUaEa : H.Ua ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdMa : H.Kd ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdUa : H.Kd ≠ H.Ua := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdEa : H.Kd ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hbufs
  have dtLv : H.Lv ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtMa : H.Ma ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtpar : par ≠ t := fun h => ht (by simp [h])
  have dtc : c ≠ t := fun h => ht (by simp [h])
  -- the binder
  unfold el1_slotBody at h
  have h := el1_bindIdx_of_reads (by exact hSz) (by change y.k ≤ n - lo; omega) h
  have h := el1_loop_one (by change 1 - (1 - y.k) = 1; omega) h
  obtain ⟨σa, ha, hrb⟩ := el1_when_bind h
  rcases Nat.lt_or_ge y.k 2 with hk | hk
  · -- a leaf of size one
    have h1 := el1_loop_one (by change 1 - (1 - (1 - (y.k - 1))) = 1; omega) ha
    have e2 := el1_loop_zero (by change 1 - (1 - (y.k - 1)) = 0; omega) hrb
    subst e2
    have h1' := (el1_leaf_congr p true y.k H.Ma H.Ua H.Ea _ _ _ _ _).symm.trans h1
    obtain ⟨hU, hE, hK, hfr, hsh, hps⟩ := holds_of_exec_eighLeafBlock
      (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
      (unif := I.sem.tapeUnif p (I.tape .uniform))
      (normal := I.sem.tapeNormal p (I.tape .gaussian)) p true y.k (A := y.A) (by exact hA)
      (by exact el1_bd_ne dUaMa) (by exact el1_bd_ne dEaMa) (by exact el1_bd_ne dUaEa)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨el1_bd_ne dKdMa, el1_bd_ne dKdUa, el1_bd_ne dKdEa⟩) h1'
    have hstep : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
        (eighTapeSample n d lo) = .leaf ((eighTapeMachine I p mmR qrR).identityMat y.k)
          fun i => (y.A i i).1 := by
      rw [eighStep, if_pos (by omega)]
    refine ⟨?_, fun q b i hW _ => ?_, hsh, hps⟩
    · unfold el1_done
      rw [hstep]
      refine ⟨⟨el1_readsIdx (k := 1) hlit htn (by omega) hK, hU,
        fun i => (hE i).trans (by simp)⟩, ?_⟩
      intro b lo' y' hl
      simp [eighLoc, hstep] at hl
    · obtain ⟨b1, b2, b3⟩ := el1_leaf_bd hkn hW
      exact hfr q b i b1 b2 b3
  · -- a node of size at least two: the window test
    have e1 := el1_loop_zero (by change 1 - (1 - (1 - (y.k - 1))) = 0; omega) ha
    subst e1
    have hY := el1_loop_one (by change 1 - (1 - (y.k - 1)) = 1; omega) hrb
    obtain ⟨a, c', v, s₂, ha', hc', hv, hw2, h⟩ := el1_inv_bin hY
    have ea : a = y.ε := Option.some_inj.mp (ha'.symm.trans hε)
    have ec : c' = R₀ := Option.some_inj.mp (hc'.symm.trans hpar.1)
    subst a c'
    have hw2' : s.store.write p t 4 v = some s₂ := hw2
    have hr2 : ∀ q b i, ¬ (b = t ∧ i = 4) → s₂.read q b i = s.store.read q b i :=
      fun q b i hne => Store.read_of_write_eq_some_of_ne hw2' (not_and_or.mp hne)
    have hsh2 : s₂.shape = s.store.shape := Store.shape_of_write_eq_some hw2'
    change exec I (.seq (.ite _ _ _ _ _ _) .skip) _ = some s' at h
    rw [exec_seq_skip, exec_ite] at h
    obtain ⟨⟨r, σc⟩, hcs, h⟩ := Option.bind_eq_some_iff.mp h
    unfold cmpStep at hcs
    obtain ⟨x1, hx1, hcs⟩ := Option.bind_eq_some_iff.mp hcs
    obtain ⟨x2, hx2, hcs⟩ := Option.bind_eq_some_iff.mp hcs
    obtain ⟨r', hr', heq⟩ := Option.map_eq_some_iff.mp hcs
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hrr, hσ⟩ := heq
    subst hσ
    subst r
    have ex1 : x1 = y.R :=
      Option.some_inj.mp (hx1.symm.trans ((hr2 _ _ _ fun h => dtLv h.1).trans hR))
    have ex2 : x2 = v := Option.some_inj.mp (hx2.symm.trans (Store.read_of_write_eq_some hw2'))
    subst x1 x2
    have hcmpM : (eighTapeMachine I p mmR qrR).le y.R
        ((eighTapeMachine I p mmR qrR).mul y.ε R₀) = r' := by
      change (I.sem.cmp p .le y.R ((I.sem.bin p .mul y.ε R₀).getD default)).getD false = r'
      rw [hv, Option.getD_some, hr', Option.getD_some]
    have hA2 : pairLayout.Holds s₂ p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A :=
      el1_holds_keep hA fun i _ _ => hr2 _ _ _ fun h => dtMa h.1
    cases r'
    · -- the node step
      simp only [Bool.false_eq_true, if_false] at h
      have hN := (el1_node_congr p mm qr n ℓ₀ F d lo y.k par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp
        c _).symm.trans h
      obtain ⟨hSu1, hSu2⟩ := hSu hk
      obtain ⟨hSg1, hSg2⟩ := hSg hk
      obtain ⟨hres, hfr, hsh, hps⟩ := holds_of_exec_eighNodeBlock_frame hmm hqr p hflag hcmp n ℓ₀ F
        d lo y.k (fun q m hm => hlit q m (by omega)) htn hkn hk H (A := y.A) (R := y.R) (R₀ := R₀)
        (ε := y.ε) (β := β) (st := { s with store := s₂, cnt := _ }) hd
        (el1_shaped_of_eq (fun b _ => by change s₂.shape[b]? = _; rw [hsh2]) hH) hbufs hA2
        ((hr2 _ _ _ fun h => dtLv h.1).trans hR) hcmpM
        ((hr2 _ _ _ fun h => dtpar h.1).trans hpar.2)
        ((hr2 _ _ _ fun h => hSu2 h.1 h.2).trans hSu1)
        (fun w hw => (hr2 _ _ _ fun h => hSg2 h.1).trans (hSg1 w hw))
        ⟨(hr2 _ _ _ fun h => dtc h.1).trans hc.1, (hr2 _ _ _ fun h => dtc h.1).trans hc.2.1,
          (hr2 _ _ _ fun h => dtc h.1).trans hc.2.2.1,
          (hr2 _ _ _ fun h => dtc h.1).trans hc.2.2.2.1,
          (hr2 _ _ _ fun h => dtc h.1).trans hc.2.2.2.2⟩ hN
      rw [← hℓ] at hres hfr
      have hsh' : s'.store.shape = s.store.shape := hsh.trans hsh2
      cases hs : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
        (eighTapeSample n d lo) with
      | leaf U e =>
        rw [hs] at hres
        exact (hres : False).elim
      | shift b A' σ =>
        rw [hs] at hres hfr
        obtain ⟨x1, x2, x3⟩ := hres
        refine ⟨?_, fun q b' i hW ht4 => ?_, hsh', hps⟩
        · unfold el1_done
          rw [hs]
          refine ⟨el1_readsIdx (k := if b then 2 else 3) hlit htn (by split <;> omega) x3, ?_⟩
          intro b' lo' y' hl
          simp only [eighLoc, hs] at hl
          by_cases hb : b' = b
          swap
          · simp [hb] at hl
          simp [hb] at hl
          obtain ⟨rfl, rfl⟩ := hl
          exact ⟨el1_readsIdx (k := y.k) hlit htn (by omega) x2, x1⟩
        · refine (hfr q b' i fun hN => hW ?_).trans (hr2 q b' i ht4)
          rcases hN with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨h1, rfl⟩
          · exact Or.inl ⟨Or.inl rfl, h1, h2⟩
          · exact Or.inr (Or.inl ⟨rfl, h1, h2⟩)
          · rcases h3 with rfl | h3
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl, by omega, rfl, rfl⟩)))
            · exact (h3 : False).elim
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, rfl⟩)))
      | split kp hkp Qp Qm Ap Am σ =>
        obtain ⟨hkp0, hkpk⟩ := el1_split_lt hs
        rw [hs] at hres hfr
        obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := hres
        refine ⟨?_, fun q b' i hW ht4 => ?_, hsh', hps⟩
        · unfold el1_done
          rw [hs]
          refine ⟨⟨el1_readsIdx (k := 4) hlit htn (by omega) x7,
            el1_readsIdx (k := kp) hlit htn (by omega) x8, x1, x2⟩, ?_⟩
          intro b' lo' y' hl
          simp only [eighLoc, hs] at hl
          cases b'
          · simp at hl
            obtain ⟨rfl, rfl⟩ := hl
            exact ⟨el1_readsIdx (k := y.k - kp) hlit htn (by omega) x6, x4⟩
          · simp at hl
            obtain ⟨rfl, rfl⟩ := hl
            exact ⟨el1_readsIdx (k := kp) hlit htn (by omega) x5, x3⟩
        · refine (hfr q b' i fun hN => hW ?_).trans (hr2 q b' i ht4)
          rcases hN with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨h1, rfl⟩
          · exact Or.inl ⟨Or.inl rfl, h1, h2⟩
          · exact Or.inr (Or.inl ⟨rfl, h1, h2⟩)
          · rcases h3 with rfl | h3
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl, by omega, Or.inl rfl,
                rfl⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo + kp, by omega, by omega, Or.inr rfl,
                h3⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, rfl⟩)))
    · -- a leaf by the window test
      simp only [if_true] at h
      have h1' := (el1_leaf_congr p false y.k H.Ma H.Ua H.Ea _ _ _ _ _).symm.trans h
      obtain ⟨hU, hE, hK, hfr, hsh, hps⟩ := holds_of_exec_eighLeafBlock
        (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
        (unif := I.sem.tapeUnif p (I.tape .uniform))
        (normal := I.sem.tapeNormal p (I.tape .gaussian)) p false y.k (A := y.A) (by exact hA2)
        (by exact el1_bd_ne dUaMa) (by exact el1_bd_ne dEaMa) (by exact el1_bd_ne dUaEa)
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨el1_bd_ne dKdMa, el1_bd_ne dKdUa, el1_bd_ne dKdEa⟩) h1'
      have hstep : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
          (eighTapeSample n d lo) = .leaf ((eighTapeMachine I p mmR qrR).identityMat y.k)
            fun _ => (eighTapeMachine I p mmR qrR).zero := by
        rw [eighStep, if_neg (by omega), if_pos hcmpM]
      refine ⟨?_, fun q b i hW ht4 => ?_, hsh.trans hsh2, hps⟩
      · unfold el1_done
        rw [hstep]
        refine ⟨⟨el1_readsIdx (k := 1) hlit htn (by omega) hK, hU,
          fun i => (hE i).trans (by simp; rfl)⟩, ?_⟩
        intro b lo' y' hl
        simp [eighLoc, hstep] at hl
      · obtain ⟨b1, b2, b3⟩ := el1_leaf_bd hkn hW
        exact (hfr q b i b1 b2 b3).trans (hr2 q b i ht4)

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP2: the window of a slot lies in the records of depth $d$ (bases, outputs, eigenvalues, kinds,
splits) and the cells of depth $d + 1$; the sizes, node matrices and parameters of depth $d$ are
outside it. -/
private theorem ep2_win_cell {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hk1 : 1 ≤ k) (hk : lo + k ≤ n) (h : el1_win H n d lo k cs b i) :
    ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) ∨
      H.LevelCell n (d + 1) b i := by
  have e1 : 2 * n * (lo + k) ≤ 2 * (n * n) := by
    rw [show 2 * (n * n) = 2 * n * n by ring]; exact Nat.mul_le_mul_left _ hk
  have e2 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have e3 : 2 * (n * n) * (d + 1 + 1) = 2 * (n * n) * (d + 1) + 2 * (n * n) := by ring
  have e4 : n * (d + 1) = n * d + n := by ring
  have e5 : n * (d + 1 + 1) = n * (d + 1) + n := by ring
  unfold el1_win at h
  unfold EighArenas.LevelCell
  rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1⟩ | ⟨hb, j, hj1, hj2, -, hj⟩
  · refine Or.inl ⟨by rcases hb with h | h <;> simp [h],
      Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩⟩
  · exact Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)
  · exact Or.inl ⟨Or.inr (Or.inr (Or.inl hb)), Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)⟩
  · refine Or.inl ⟨by rcases hb with h | h <;> simp [h],
      Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩)⟩
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hb), by omega, by omega⟩))

set_option maxHeartbeats 1600000 in
-- The run unfolds the scope, seven instructions, two draw loops and the loop over the slots.
/-- EP2: `NLAlib.holds_of_exec_eighDownLevel` with the finer frame of its proof: of the cells of
depth $d$ only the records (bases, outputs, eigenvalues, kinds, splits) may change. -/
private theorem ep2_holds_of_exec_eighDownLevel {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st st' : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hnext : ∀ lo < n, ReadsIdx I.sem st.store p H.Sz (n * (d + 1) + lo) 0)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su Sg
      H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st = some st') :
    H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) ∧
      H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, b ≠ Su → b ≠ Sg →
        ¬ ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) →
        ¬ H.LevelCell n (d + 1) b i → st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos .uniform = st.pos .uniform + n ∧
      st'.pos .gaussian = st.pos .gaussian + 4 * (n * n) := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hlev1, hlev2, hlev3, hlev4⟩ := hlev
  set tH := st.store.size with htH
  set S0 : Store P K := st.store.push (p, Array.replicate (5 : IExp ℕ).eval none) with hS0
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  obtain ⟨z0, o1, -, hl1, -, -⟩ := id hflag
  have lpar := Store.lt_size_of_read_eq_some hpar.1
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans hl1)
  have lMa := hsz hMa
  have lUa := hsz hUa
  have lQa := hsz hQa
  have lEa := hsz hEa
  have lSz := hsz hSzs
  have lKd := hsz hKd
  have lKp := hsz hKp
  have lLv := hsz hLv
  have dLvc : H.Lv ≠ c := fun h => by simp [EighArenas.handles, h] at hbufs
  have dLvSu : H.Lv ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dLvSg : H.Lv ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzSu : H.Sz ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzSg : H.Sz ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzLv : H.Sz ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSu : H.Ma ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSg : H.Ma ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaLv : H.Ma ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSu : par ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSg : par ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparLv : par ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSu : c ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSg : c ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSuSg : Su ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have hpb : par ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hcb : c ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hSub : Su ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hSgb : Sg ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hLvb : H.Lv ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hnd
  have hwinb : ∀ {lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}, el1_win H n d lo k cs b i →
      b < st.store.size := fun hw => by
    have := el1_win_buf hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  -- the scope
  change exec I (.seq (.alloc p _ _) .skip) st = some st' at h
  obtain ⟨s₂, h₀, e₀⟩ := el1_alloc_inv h
  subst e₀
  clear h
  -- the parameters of depth d + 1
  obtain ⟨v0, S1, hv0, hw0, h⟩ := el1_inv_litIdx h₀
  obtain ⟨a1, b1, v1, S2, ha1, hb1, hv1, hw1, h⟩ := el1_inv_bin h
  obtain ⟨a2, b2, v2, S3, ha2, hb2, hv2, hw2, h⟩ := el1_inv_bin h
  obtain ⟨a3, b3, v3, S4, ha3, hb3, hv3, hw3, h⟩ := el1_inv_bin h
  obtain ⟨a4, b4, v4, S5, ha4, hb4, hv4, hw4, h⟩ := el1_inv_bin h
  obtain ⟨a5, b5, v5, S6, ha5, hb5, hv5, hw5, h⟩ := el1_inv_bin h
  obtain ⟨a6, b6, v6, S7, ha6, hb6, hv6, hw6, h⟩ := el1_inv_bin h
  have hv0' : I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ) = some v0 := hv0
  have hw0' : S0.write p tH 0 v0 = some S1 := hw0
  have hw1' : S1.write p tH 2 v1 = some S2 := hw1
  have hw2' : S2.write p tH 3 v2 = some S3 := hw2
  have hw3' : S3.write p H.Lv (2 * (d + 1)) v3 = some S4 := hw3
  have hw4' : S4.write p tH 1 v4 = some S5 := hw4
  have hw5' : S5.write p tH 3 v5 = some S6 := hw5
  have hw6' : S6.write p H.Lv (2 * (d + 1) + 1) v6 = some S7 := hw6
  have hr0 : ∀ q b i, b < tH → S0.read q b i = st.store.read q b i :=
    fun q b i hb => Store.read_push_of_lt hb
  have dcT : c ≠ tH := by omega
  have dLvT : H.Lv ≠ tH := by omega
  -- the reads of the seven instructions
  have ea1 : S1.read p c 1 = st.store.read p c 1 := by
    rw [Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have ea2 : S2.read p c 2 = st.store.read p c 2 := by
    rw [Store.read_of_write_eq_some_of_ne hw1' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have eb3 : S3.read p H.Lv (2 * d) = st.store.read p H.Lv (2 * d) := by
    rw [Store.read_of_write_eq_some_of_ne hw2' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dLvT), hr0 _ _ _ lLv]
  have ea4 : S4.read p c 0 = st.store.read p c 0 := by
    rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inl dLvc.symm),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have eb4 : S4.read p tH 0 = some v0 := by
    rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inl dLvT.symm),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inr (by omega)),
      Store.read_of_write_eq_some hw0']
  have ea5 : S5.read p c 0 = st.store.read p c 0 := by
    rw [Store.read_of_write_eq_some_of_ne hw4' (Or.inl dcT), ea4]
  have eb6 : S6.read p H.Lv (2 * d + 1) = st.store.read p H.Lv (2 * d + 1) := by
    rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dLvT), hr0 _ _ _ lLv]
  have hb1' : b1 = v0 := Option.some_inj.mp (hb1.symm.trans (Store.read_of_write_eq_some hw0'))
  have hb2' : b2 = v1 := Option.some_inj.mp (hb2.symm.trans (Store.read_of_write_eq_some hw1'))
  have ha3' : a3 = v2 := Option.some_inj.mp (ha3.symm.trans (Store.read_of_write_eq_some hw2'))
  have hb4' : b4 = v0 := Option.some_inj.mp (hb4.symm.trans eb4)
  have hb5' : b5 = v4 := Option.some_inj.mp (hb5.symm.trans (Store.read_of_write_eq_some hw4'))
  have ha6' : a6 = v5 := Option.some_inj.mp (ha6.symm.trans (Store.read_of_write_eq_some hw5'))
  have ha1' : some a1 = I.sem.lit p ((2 : ℕ) : ℚ) := (ha1.symm.trans ea1).trans hc.2.1
  have ha2' : some a2 = some (M.div M.one (M.ofNat 2)) := (ha2.symm.trans ea2).trans hc.2.2.1
  have hb3' : some b3 = some (eighLevelParams M R₀ ε ℓ₀ d).1 := (hb3.symm.trans eb3).trans hlev3
  have ha4' : some a4 = I.sem.lit p 1 := (ha4.symm.trans ea4).trans hc.1
  have ha5' : some a5 = I.sem.lit p 1 := (ha5.symm.trans ea5).trans hc.1
  have hb6' : some b6 = some (eighLevelParams M R₀ ε ℓ₀ d).2 :=
    (hb6.symm.trans eb6).trans hlev4
  subst b1 b2 a3 b4 b5 a6
  -- the machine's values
  have mOne : M.one = a4 := by
    change (I.sem.lit p 1).getD default = a4
    rw [← ha4', Option.getD_some]
  have ea45 : a5 = a4 := Option.some_inj.mp (ha5'.trans ha4'.symm)
  subst a5
  have mTwo : M.ofNat 2 = a1 := by
    change (I.sem.lit p ((2 : ℕ) : ℚ)).getD default = a1
    rw [← ha1', Option.getD_some]
  have mL : M.ofNat (ℓ₀ + d) = v0 := by
    change (I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD default = v0
    rw [hv0', Option.getD_some]
  have hP1 : (eighLevelParams M R₀ ε ℓ₀ (d + 1)).1 = v3 := by
    change M.mul (M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat (ℓ₀ + d))))
      (eighLevelParams M R₀ ε ℓ₀ d).1 = v3
    rw [← Option.some_inj.mp hb3', ← Option.some_inj.mp ha2', mTwo, mL]
    change (I.sem.bin p .mul ((I.sem.bin p .add a2 ((I.sem.bin p .div a1 v0).getD default)).getD
      default) b3).getD default = v3
    rw [hv1, Option.getD_some, hv2, Option.getD_some, hv3, Option.getD_some]
  have hP2 : (eighLevelParams M R₀ ε ℓ₀ (d + 1)).2 = v6 := by
    change M.mul (M.sub M.one (M.div M.one (M.ofNat (ℓ₀ + d))))
      (eighLevelParams M R₀ ε ℓ₀ d).2 = v6
    rw [← Option.some_inj.mp hb6', mOne, mL]
    change (I.sem.bin p .mul ((I.sem.bin p .sub a4 ((I.sem.bin p .div a4 v0).getD default)).getD
      default) b6).getD default = v6
    rw [hv4, Option.getD_some, hv5, Option.getD_some, hv6, Option.getD_some]
  -- the frame of the seven instructions
  have hr7 : ∀ q b i, b < tH → ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      S7.read q b i = st.store.read q b i := by
    intro q b i hb hL
    have hbT : b ≠ tH := by omega
    have hL' : b ≠ H.Lv ∨ (i ≠ 2 * (d + 1) ∧ i ≠ 2 * (d + 1) + 1) := by
      by_cases h' : b = H.Lv
      · exact Or.inr ⟨fun h'' => hL ⟨h', Or.inl h''⟩, fun h'' => hL ⟨h', Or.inr h''⟩⟩
      · exact Or.inl h'
    rw [Store.read_of_write_eq_some_of_ne hw6' (hL'.imp_right And.right),
      Store.read_of_write_eq_some_of_ne hw5' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw3' (hL'.imp_right And.left),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl hbT), hr0 _ _ _ hb]
  have hL1 : S7.read p H.Lv (2 * (d + 1)) = some v3 := by
    rw [Store.read_of_write_eq_some_of_ne hw6' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw5' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl dLvT), Store.read_of_write_eq_some hw3']
  have hL2 : S7.read p H.Lv (2 * (d + 1) + 1) = some v6 := Store.read_of_write_eq_some hw6'
  have hsh7 : S7.shape = S0.shape := by
    rw [Store.shape_of_write_eq_some hw6', Store.shape_of_write_eq_some hw5',
      Store.shape_of_write_eq_some hw4', Store.shape_of_write_eq_some hw3',
      Store.shape_of_write_eq_some hw2', Store.shape_of_write_eq_some hw1',
      Store.shape_of_write_eq_some hw0']
  -- the draws
  obtain ⟨σu, hu, h⟩ := el1_seq h
  obtain ⟨σg, hg, h⟩ := el1_seq h
  obtain ⟨σe, he, h⟩ := el1_seq h
  rw [exec_skip, Option.some_inj] at h
  subst s₂
  obtain ⟨hush, hupos, hurd, hufr⟩ := el1_draw_loop hu
  obtain ⟨hgsh, hgpos, hgrd, hgfr⟩ := el1_draw_loop hg
  have hshg : σg.store.shape = S0.shape := hgsh.trans (hush.trans hsh7)
  have hSuR : ∀ w < n, σg.store.read p Su w = some (I.tape .uniform (n * d + w)) := by
    intro w hw
    rw [hgfr _ _ _ (Or.inl dSuSg), hurd w hw]
    change some (I.tape .uniform (st.pos .uniform + w)) = _
    rw [hpos.1]
  have hSgR : ∀ w < 4 * (n * n), σg.store.read p Sg w =
      some (I.tape .gaussian (4 * (n * n) * d + w)) := by
    intro w hw
    rw [hgrd w hw, hupos]
    simp [hpos.2]
  have hrg : ∀ q b i, b < tH → b ≠ Su → b ≠ Sg →
      ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      σg.store.read q b i = st.store.read q b i := fun q b i hb h1 h2 h3 => by
    rw [hgfr _ _ _ (Or.inl h2), hufr _ _ _ (Or.inl h1)]
    exact hr7 q b i hb h3
  have hS0sz : S0.size = tH + 1 := by rw [hS0, Array.size_push, htH]
  have hshape5 : S0.shape[tH]? = some (p, 5) := Store.getElem?_shape_push_size _ _ _
  have hSut : Su = tH → 1 ≤ n → n ≤ 5 := by
    intro hS hn
    obtain ⟨len, hlen, hi⟩ := Store.exists_getElem?_shape_of_read_eq_some (hSuR (n - 1) (by omega))
    rw [hshg, hS, hshape5, Option.some.injEq, Prod.mk.injEq] at hlen
    omega
  have hSgt : Sg = tH → 1 ≤ n → 4 * (n * n) ≤ 5 := by
    intro hS hn
    have hn2 : 0 < 4 * (n * n) := by positivity
    obtain ⟨len, hlen, hi⟩ :=
      Store.exists_getElem?_shape_of_read_eq_some (hSgR (4 * (n * n) - 1) (by omega))
    rw [hshg, hS, hshape5, Option.some.injEq, Prod.mk.injEq] at hlen
    omega
  have hH0 : H.Shaped σg.store p n D :=
    el1_shaped_of_eq (fun b hb => by
      rw [hshg, hS0, Store.getElem?_shape_push_of_lt _ (by
        simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)]) hH
  have htb : tH ∉ H.handles ++ [par, c] := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    omega
  have hnd' : H.handles.Nodup := hnd
  -- nodes of depth d: bounds and uniqueness
  have hbnd : ∀ {a : List Bool} {lo : ℕ} {y : EighNode K},
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) → 1 ≤ y.k →
        1 ≤ n ∧ lo + y.k ≤ n := by
    intro a lo y hl hk
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      cases a with
      | nil =>
        simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨-, rfl⟩ := hl
        exact absurd hk (by simp [hn])
      | cons b a =>
        have h0 : n ≤ 1 := by omega
        simp [eighLoc, eighStep, h0] at hl
    · exact ⟨hn, (eighLoc_bounds hn hl).2⟩
  have huniq : ∀ {a a' : List Bool} {lo : ℕ} {y y' : EighNode K}, a.length = d →
      a'.length = d → eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) →
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo, y') → 1 ≤ n → y = y' := by
    intro a a' lo y y' ha ha' hl hl' hn
    by_cases hae : a = a'
    · subst hae
      rw [hl] at hl'
      simp only [Option.some.injEq, Prod.mk.injEq] at hl'
      exact hl'.2
    · have h1 := (eighLoc_bounds hn hl).1
      have h2 := (eighLoc_bounds hn hl').1
      rcases eighLoc_disjoint (ha.trans ha'.symm) hae hl hl' with h | h <;> omega
  -- the loop over the slots
  have hinv := forall_of_exec_loop_eq_some I (fun w (s : St P K C) =>
      s.store.shape = σg.store.shape ∧ s.pos = σg.pos ∧
      (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
        el1_done H I.sem s.store p M n F d R₀ β lo y) ∧
      ∀ q b i, (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
          ¬ el1_win H n d lo y.k (el1_childSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ
            (eighTapeSample n d lo)) lo) b i) → ¬ (b = tH ∧ i = 4) →
        s.store.read q b i = σg.store.read q b i)
    ⟨rfl, rfl, fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl⟩ ?_ he
  swap
  · rintro w hw s₁ s₂ ⟨hsh1, hps1, hdn1, hfr1⟩ hex
    change w < n at hw
    have hn1 : 1 ≤ n := by omega
    have hrd1 : ∀ q b i, b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] → ¬ (b = tH ∧ i = 4) →
        s₁.store.read q b i = σg.store.read q b i :=
      fun q b i hb ht => hfr1 q b i (fun _ _ _ _ => el1_not_win_buf hb) ht
    have hSz1 : ∀ i, i < n * (d + 1) → s₁.store.read p H.Sz i = st.store.read p H.Sz i :=
      fun i hi => (hfr1 _ _ _ (fun _ _ _ _ => el1_not_win_Sz hnd' hi) (fun h => by omega)).trans
        (hrg _ _ _ lSz dSzSu dSzSg fun h => dSzLv h.1)
    have he4 : (n * (d + 1)) = n * d + n := by ring
    by_cases hnode : ∃ (y : EighNode K) (a : List Bool), a.length = d ∧
        eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y)
    · obtain ⟨y, a, ha, hl⟩ := hnode
      obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn1 hl
      obtain ⟨hyR, hyε, hyℓ⟩ := eighLoc_params hl
      rw [ha] at hyR hyε hyℓ
      have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
      have e5 : 2 * n * w + 2 * (n * y.k) ≤ 2 * (n * n) := by
        have := Nat.mul_le_mul_left (2 * n) hkn
        nlinarith
      have e6 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
      obtain ⟨hdone, hfrW, hsh2, hps2⟩ := el1_slot_node hmm hqr p hflag hcmp n ℓ₀ F d D hd hlit htn
        H
        (par := par) (Su := Su) (Sg := Sg) (c := c) (t := tH) (s := s₁) (s' := s₂) (R₀ := R₀)
        (β := β) hk1 hkn hyℓ (el1_shaped_of_eq (fun b _ => by rw [hsh1]) hH0) hbufs htb
        (el1_readsIdx_congr (hSz1 _ (by omega)) (hlev1 a w y ha hl).1)
        (el1_holds_keep (hlev1 a w y ha hl).2 fun i h1 h2 =>
          (hfr1 _ _ _ (fun _ _ _ _ => el1_not_win_Ma hnd' (by omega)) (fun h => by omega)).trans
            (hrg _ _ _ lMa dMaSu dMaSg fun h => dMaLv h.1))
        (by
          rw [hrd1 p H.Lv (2 * d) hLvb (fun h => by omega),
            hrg p H.Lv (2 * d) lLv dLvSu dLvSg (fun h => by omega)]
          exact hlev3.trans (congrArg some hyR.symm))
        (by
          rw [hrd1 p H.Lv (2 * d + 1) hLvb (fun h => by omega),
            hrg p H.Lv (2 * d + 1) lLv dLvSu dLvSg (fun h => by omega)]
          exact hlev4.trans (congrArg some hyε.symm))
        ⟨by rw [hrd1 p par 0 hpb (fun h => by omega),
              hrg p par 0 lpar dparSu dparSg (fun h => dparLv h.1), hpar.1],
          by rw [hrd1 p par 2 hpb (fun h => by omega),
              hrg p par 2 lpar dparSu dparSg (fun h => dparLv h.1), hpar.2]⟩
        (fun hk2 => by
          have hSu4 : Su = tH → w ≠ 4 := fun hS => by have := hSut hS hn1; omega
          exact ⟨(hrd1 _ _ _ hSub fun h => hSu4 h.1 h.2).trans (hSuR w hw), hSu4⟩)
        (fun hk2 => by
          have hSgT : Sg ≠ tH := fun hS => by
            have := hSgt hS hn1
            have : 2 ≤ n := by omega
            nlinarith
          exact ⟨fun w' hw' => (hrd1 _ _ _ hSgb fun h => hSgT h.1).trans (hSgR w' hw'), hSgT⟩)
        ⟨by rw [hrd1 p c 0 hcb (fun h => by omega),
              hrg p c 0 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.1],
          by rw [hrd1 p c 1 hcb (fun h => by omega),
              hrg p c 1 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.1],
          by rw [hrd1 p c 2 hcb (fun h => by omega),
              hrg p c 2 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.1],
          by rw [hrd1 p c 3 hcb (fun h => by omega),
              hrg p c 3 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.2.1],
          by rw [hrd1 p c 4 hcb (fun h => by omega),
              hrg p c 4 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.2.2]⟩ hex
      refine ⟨hsh2.trans hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
        fun q b i hall ht4 => ?_⟩
      · obtain ⟨a', ha', hl'⟩ := hn'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
        · have hk1' := (eighLoc_bounds hn1 hl').1
          have hkn' := (eighLoc_bounds hn1 hl').2
          have hdis : lo + y'.k ≤ w := by
            have hae : a' ≠ a := fun h => by
              subst h
              rw [hl] at hl'
              have := (Prod.mk.inj (Option.some_inj.mp hl')).1
              omega
            rcases eighLoc_disjoint (ha'.trans ha.symm) hae hl' hl with h | h <;> omega
          exact el1_done_congr hk1' hkn' (fun b i hwin => hfrW p b i
            (fun hw' => el1_win_disjoint hnd' hk1' hdis hwin hw')
            (fun h => by have := hwinb hwin; omega)) (hdn1 lo y' hlo ⟨a', ha', hl'⟩)
        · rw [← huniq ha ha' hl hl' hn1]
          exact hdone
      · rw [hfrW q b i (hall w y (Nat.lt_succ_self w) ⟨a, ha, hl⟩) ht4]
        exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4
    · have hSz0 := hlev2 w hw (fun a y ha hl => hnode ⟨y, a, ha, hl⟩)
      obtain ⟨hst, hps2⟩ := el1_slot_skip (s := s₁) (s' := s₂)
        (el1_readsIdx_congr (hSz1 _ (by omega)) hSz0) hex
      refine ⟨by rw [hst]; exact hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
        fun q b i hall ht4 => ?_⟩
      · rw [hst]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
        · exact hdn1 lo y' hlo hn'
        · obtain ⟨a', ha', hl'⟩ := hn'
          exact absurd ⟨y', a', ha', hl'⟩ hnode
      · rw [hst]
        exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4
  obtain ⟨hshe, hpse, hdne, hfre⟩ := hinv
  -- the pops
  have hSsz : σe.store.size = tH + 1 := by
    rw [Store.size_eq_of_shape_eq (hshe.trans hshg), hS0sz]
  have hpop : ∀ q b i, b < tH → Store.read (Array.pop σe.store) q b i = σe.store.read q b i :=
    fun q b i hb => Store.read_pop_of_lt (by omega)
  have hpopsz : (Array.pop σe.store).size = tH := by simp [Array.size_pop, hSsz]
  have hdoneF : ∀ (a : List Bool) (lo : ℕ) (y : EighNode K), a.length = d →
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) → 1 ≤ y.k →
        el1_done H I.sem (Array.pop σe.store) p M n F d R₀ β lo y := by
    intro a lo y ha hl hk1
    obtain ⟨hn1, hkn⟩ := hbnd hl hk1
    exact el1_done_congr hk1 hkn (fun b i hwin => hpop p b i (hwinb hwin))
      (hdne lo y (by change lo < n; omega) ⟨a, ha, hl⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold EighArenas.LevelHolds
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- the children
      intro a' lo' y' ha' hl'
      obtain ⟨a, b, rfl⟩ : ∃ a b, a' = a ++ [b] := by
        rcases List.eq_nil_or_concat a' with h0 | ⟨L, b, h0⟩
        · subst h0; simp at ha'
        · exact ⟨L, b, by simpa using h0⟩
      have ha : a.length = d := by simpa using ha'
      rw [eighLoc_append_singleton] at hl'
      obtain ⟨⟨lo, y⟩, hl, hl2⟩ := Option.bind_eq_some_iff.mp hl'
      simp only [ha, Nat.zero_add] at hl2
      have hk1 : 1 ≤ y.k := by
        by_contra h0
        have h0' : y.k ≤ 1 := by omega
        simp [eighLoc, eighStep, h0'] at hl2
      exact (hdoneF a lo y ha hl hk1).2 b lo' y' hl2
    · -- the slots that start no node
      intro lo' hlo' hno
      refine el1_readsIdx_congr ?_ (hnext lo' hlo')
      rw [hpop p H.Sz (n * (d + 1) + lo') lSz,
        hfre p H.Sz (n * (d + 1) + lo') ?_ (fun h => by omega),
        hrg p H.Sz (n * (d + 1) + lo') lSz dSzSu dSzSg fun h => dSzLv h.1]
      intro lo y _ ⟨a, ha, hl⟩ hwin
      obtain ⟨j, hj, hij⟩ := el1_win_Sz hnd' hwin
      have hj' : j = lo' := by omega
      subst hj'
      obtain ⟨b, y', hl2⟩ := el1_childSlot_loc hj
      refine hno (a ++ [b]) y' (by simp [ha]) ?_
      rw [eighLoc_append_singleton, hl, Option.bind_some]
      simpa [ha] using hl2
    · rw [hpop p H.Lv (2 * (d + 1)) lLv,
        hfre p H.Lv (2 * (d + 1)) (fun _ _ _ _ => el1_not_win_buf hLvb) (fun h => by omega),
        hgfr p H.Lv (2 * (d + 1)) (Or.inl dLvSg), hufr p H.Lv (2 * (d + 1)) (Or.inl dLvSu), hL1]
      exact congrArg some hP1.symm
    · rw [hpop p H.Lv (2 * (d + 1) + 1) lLv,
        hfre p H.Lv (2 * (d + 1) + 1) (fun _ _ _ _ => el1_not_win_buf hLvb) (fun h => by omega),
        hgfr p H.Lv (2 * (d + 1) + 1) (Or.inl dLvSg), hufr p H.Lv (2 * (d + 1) + 1) (Or.inl dLvSu),
        hL2]
      exact congrArg some hP2.symm
  · -- the records
    unfold EighArenas.RecordHolds
    intro a lo y ha hl hk1
    exact (hdoneF a lo y ha hl hk1).1
  · -- the frame
    intro q b i hbSu hbSg h1 h2
    by_cases hb : b < tH
    · rw [hpop q b i hb, hfre q b i ?_ (fun h => by omega)]
      · exact hrg q b i hb hbSu hbSg fun h => h2 (Or.inr (Or.inr h))
      · intro lo y hlo ⟨a, ha, hl⟩ hwin
        change lo < n at hlo
        have hn1 : 1 ≤ n := by omega
        rcases ep2_win_cell (eighLoc_bounds hn1 hl).1 (eighLoc_bounds hn1 hl).2 hwin with
          h | h
        · exact h1 h
        · exact h2 h
    · rw [Store.read_eq_none_of_size_le (s := Array.pop σe.store) (q := q) (b := b) (i := i)
        (by omega), Store.read_eq_none_of_size_le (s := st.store) (q := q) (b := b) (i := i)
        (by omega)]
  · change Store.shape (Array.pop σe.store) = _
    rw [Store.shape_pop, hshe, hshg, hS0]
    simp [Store.shape]
  · change σe.pos .uniform = _
    rw [hpse, hgpos, hupos]
    simp
  · change σe.pos .gaussian = _
    rw [hpse, hgpos, hupos]
    simp

/-- **One level of the downward pass**: let the kernels of `I` be the routines `mmR`, `qrR` on
interleaved pairs, the semantics decide flags, with exact integer literals up to $n + 4$ and the
exact floor conversion; $M$ = `NLAlib.eighTapeMachine I p mmR qrR` and the root
$(n, \mathbf{A}, R_0, \varepsilon, \ell_0)$. A successful run of `NLAlib.eighDownLevel` at depth
$d < D$ from a state whose arenas hold the nodes of depth $d$ (`NLAlib.EighArenas.LevelHolds`) and
whose size cells of depth $d + 1$ all read $0$, with the tape positions $nd$ (uniform) and
$4n^2 d$ (Gaussian), the stored $R_0$, $\varepsilon$, $\beta$ in `par` and the constants in `c`
(cells $0$ to $4$: one, $\mathrm{fl}(2)$, $\mathrm{fl}(1/2)$, $-1$, the stored $\sqrt{1/2}$),
ends with the arenas holding the nodes of depth $d + 1$ and the
records of depth $d$ (`NLAlib.EighArenas.RecordHolds`); every cell outside depths $d$ and $d + 1$ of
the arenas and the sample buffers `Su`, `Sg` is unchanged, the store shape too, and the tape
positions advance by $n$ and $4n^2$. No printed source.
Proof: the parameters of depth $d + 1$ by seven instructions (`NLAlib.eighNextParams` at
$\ell_0 + d$, `NLAlib.eighLevelParams`); the draws by `NLAlib.Computation.exec_forRange_draw` (cell
$i$ of `Su` is the tape at $nd + i$, cell $w$ of `Sg` at $4n^2 d + w$); then the loop over the slots
by `NLAlib.Computation.forall_of_exec_loop_eq_some` (pilot) with the invariant "the slots below $lo$
are done": at slot $lo$ the binder reads the stored size (`hlev`, `NLAlib.ReadsIdx`, within the
bound $n - lo$ by `NLAlib.eighLoc_bounds`), a slot that starts no node reads $0$ and skips
(`NLAlib.eighWhen`), and a node of size $k$ runs a leaf (`NLAlib.holds_of_exec_eighLeafBlock`, for
$k \le 1$ or $R \le \mathrm{fl}(\varepsilon R_0)$, one comparison) or
`NLAlib.holds_of_exec_eighNodeBlock`, whose window, tolerance and depth counter are the depth's
(`NLAlib.eighLoc_params`); its writes stay in its own range of depths $d$ and $d + 1$
(`NLAlib.eighLoc_disjoint`), so the other nodes' cells are kept, and the children of the nodes of
depth $d$ are the nodes of depth $d + 1$ (`NLAlib.eighLoc_append_singleton`); the sizes of the
children read back by `NLAlib.Computation.IsExactIntLit.toNat_eq_of_lit_eq_some` (scaffold,
$k \le n$), and every other slot of depth $d + 1$ keeps its $0$. L, about 200 lines (split the
per-slot step into a private lemma). -/
theorem holds_of_exec_eighDownLevel {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st st' : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hnext : ∀ lo < n, ReadsIdx I.sem st.store p H.Sz (n * (d + 1) + lo) 0)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su Sg
      H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st = some st') :
    H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) ∧
      H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, b ≠ Su → b ≠ Sg → ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos .uniform = st.pos .uniform + n ∧
      st'.pos .gaussian = st.pos .gaussian + 4 * (n * n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ep2_holds_of_exec_eighDownLevel hmm hqr p hflag hcmp n ℓ₀ F d
    D hd
    hlit htn H hH hbufs hlev hnext hpos hpar hc h
  exact ⟨h1, h2, fun q b i hSu hSg hd1 hd2 => h3 q b i hSu hSg (fun h => hd1 h.2) hd2, h4, h5, h6⟩

/-! #### Helpers of `NLAlib.exists_exec_eighDownLevel` -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL2: a mapped option is some when the option is. -/
private theorem el2_map_ex {α β : Type} {o : Option α} {f : α → β} (h : ∃ a, o = some a) :
    ∃ b, o.map f = some b := by
  obtain ⟨a, ha⟩ := h
  exact ⟨f a, by rw [ha]; rfl⟩

omit [Inhabited K] in
/-- EL2: a sequence succeeds when its first part does and the rest succeeds from there. -/
private theorem el2_ex_seq {a b : Stmt P ι ℕ ℕ} {s s₁ : St P K C} (h₁ : exec I a s = some s₁)
    (h₂ : ∃ st', exec I b s₁ = some st') : ∃ st', exec I (.seq a b) s = some st' := by
  obtain ⟨t, ht⟩ := h₂
  exact ⟨t, by rw [exec_seq, h₁, Option.bind_some, ht]⟩

omit [Inhabited K] in
/-- EL2: a goal on a state, for a named state equal to it. -/
private theorem el2_name {X : Stmt P ι ℕ ℕ} {s : St P K C}
    (h : ∀ σ : St P K C, σ = s → ∃ st', exec I X σ = some st') : ∃ st', exec I X s = some st' :=
  h s rfl

omit [Inhabited K] in
/-- EL2: an index literal, then the rest. -/
private theorem el2_ex_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {v : K} {s' : Store P K} (hv : I.sem.lit p (e.eval : ℚ) = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some st') :
    ∃ st', exec I (.seq (.instr (.litIdx p dst e)) t) s = some st' := by
  rw [exec_seq_instr_litIdx I hv hw]
  exact h

omit [Inhabited K] in
/-- EL2: a binary operation, then the rest. -/
private theorem el2_ex_bin {p : P} {b : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {a c v : K} {s' : Store P K} (hx : s.store.read p x.buf x.idx.eval = some a)
    (hy : s.store.read p y.buf y.idx.eval = some c) (hv : I.sem.bin p b a c = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p b) } = some st') :
    ∃ st', exec I (.seq (.instr (.bin p b dst x y)) t) s = some st' := by
  rw [exec_seq_instr_bin I hx hy hv hw]
  exact h

omit [Inhabited K] in
/-- EL2: a scoped index binder on a stored size within its bound. -/
private theorem el2_ex_bindIdx {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} {k : ℕ}
    (hr : ReadsIdx I.sem st.store p x.buf x.idx.eval k) (hk : k ≤ bound.eval)
    (h : ∃ st', exec I (body k) { st with cnt := st.cnt + I.charge (.toNat p) } = some st') :
    ∃ st', exec I (.seq (.bindIdx p x bound body) .skip) st = some st' := by
  unfold ReadsIdx at hr
  obtain ⟨w, hw, hv⟩ := Option.bind_eq_some_iff.mp hr
  rw [exec_seq_skip, exec_bindIdx_of_read I hw hv hk]
  exact h

omit [Inhabited K] in
/-- EL2: a loop of one iteration, then nothing. -/
private theorem el2_when1_eq {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s : St P K C}
    (he : e.eval = 1) : exec I (.seq (.loop e b) .skip) s = exec I (b 0) s := by
  rw [exec_seq_skip, exec_loop, he]
  simp [List.range_one]

omit [Inhabited K] in
/-- EL2: a loop of no iteration, then nothing. -/
private theorem el2_when0_eq {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s : St P K C}
    (he : e.eval = 0) : exec I (.seq (.loop e b) .skip) s = some s := by
  rw [exec_seq_skip, exec_loop, he]
  rfl

omit [Inhabited K] in
/-- EL2: a loop of one iteration that succeeds. -/
private theorem el2_ex_when1 {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s : St P K C}
    (he : e.eval = 1) (h : ∃ st', exec I (b 0) s = some st') :
    ∃ st', exec I (.seq (.loop e b) .skip) s = some st' := by
  rw [el2_when1_eq he]
  exact h

omit [Inhabited K] in
/-- EL2: a guarded block, then the rest. -/
private theorem el2_ex_whenBind {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {s σ : St P K C}
    (h₁ : exec I (eighWhen e b).run s = some σ) (h₂ : ∃ st', exec I (f ()).run σ = some st') :
    ∃ st', exec I (eighWhen e b >>= f).run s = some st' := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl), h₁, Option.bind_some]
  exact h₂

omit [Inhabited K] in
/-- EL2: a conditional on a comparison of stored cells, then nothing. -/
private theorem el2_ex_ite {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {t e : Stmt P ι ℕ ℕ}
    {st : St P K C} {a b : K} {r : Bool} (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some b) (hc : I.sem.cmp p c a b = some r)
    (h : ∃ st', (if r then exec I t { st with cnt := st.cnt + I.charge (.cmp p) }
      else exec I e { st with cnt := st.cnt + I.charge (.cmp p) }) = some st') :
    ∃ st', exec I (.seq (.ite p c x y t e) .skip) st = some st' := by
  rw [exec_seq_skip, exec_ite]
  simp only [cmpStep, hx, hy, hc, Option.bind_some, Option.map_some]
  exact h

/-- EL2: an arithmetic operation of the standard model succeeds, with its rounding. -/
private theorem el2_bin {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) {b : BinOp} (hb : b.IsArith)
    {x y : K} (hy : b = .div → dec p y ≠ 0) :
    ∃ z, I.sem.bin p b x y = some z ∧
      ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = b.realOp (dec p x) (dec p y) * (1 + δ) := by
  obtain ⟨z, hz⟩ := hsem.bin_ok p b x y hb hy trivial
  exact ⟨z, hz, hsem.bin_err p b x y z hb hz⟩

omit [Inhabited K] in
/-- EL2: a literal into a cell of a buffer, then nothing, succeeds and keeps the other buffers. -/
private theorem el2_body_lit {p : P} {Y len : ℕ} {i : IExp ℕ} {q₀ : ℚ} {s : St P K C}
    (hz : ∃ z, I.sem.lit p q₀ = some z) (hY : s.store.shape[Y]? = some (p, len))
    (hi : i.eval < len) :
    ∃ s', exec I (.seq (.instr (.lit p ⟨Y, i⟩ q₀)) .skip) s = some s' ∧
      s'.store.shape = s.store.shape ∧ ∀ q b j, b ≠ Y → s'.store.read q b j = s.store.read q b j := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s', hw⟩ := Store.exists_write_eq_some_of_getElem?_shape z hY hi
  refine ⟨_, (exec_seq_instr_lit I hz hw).trans (exec_skip I _), Store.shape_of_write_eq_some hw,
    fun q b j hb => Store.read_of_write_eq_some_of_ne hw (Or.inl hb)⟩

omit [Inhabited K] in
/-- EL2: a copy into a cell of a buffer, then nothing, succeeds and keeps the other buffers. -/
private theorem el2_body_copy {p : P} {Y len : ℕ} {i : IExp ℕ} {src : Cell ℕ ℕ} {s : St P K C}
    (hx : ∃ v, s.store.read p src.buf src.idx.eval = some v)
    (hY : s.store.shape[Y]? = some (p, len)) (hi : i.eval < len) :
    ∃ s', exec I (.seq (.instr (.copy p ⟨Y, i⟩ src)) .skip) s = some s' ∧
      s'.store.shape = s.store.shape ∧ ∀ q b j, b ≠ Y → s'.store.read q b j = s.store.read q b j := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨s', hw⟩ := Store.exists_write_eq_some_of_getElem?_shape v hY hi
  refine ⟨_, (exec_seq_instr_copy I hv hw).trans (exec_skip I _), Store.shape_of_write_eq_some hw,
    fun q b j hb => Store.read_of_write_eq_some_of_ne hw (Or.inl hb)⟩

omit [Inhabited K] in
/-- EL2: a loop whose steps succeed, keeping the shape and the buffers other than `Y`. -/
private theorem el2_loop {m : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {Y : ℕ} {st : St P K C}
    (hstep : ∀ w < m.eval, ∀ s : St P K C, s.store.shape = st.store.shape →
      (∀ q b j, b ≠ Y → s.store.read q b j = st.store.read q b j) →
      ∃ s', exec I (body w) s = some s' ∧ s'.store.shape = s.store.shape ∧
        ∀ q b j, b ≠ Y → s'.store.read q b j = s.store.read q b j) :
    ∃ st', exec I (.loop m body) st = some st' ∧ st'.store.shape = st.store.shape ∧
      ∀ q b j, b ≠ Y → st'.store.read q b j = st.store.read q b j := by
  obtain ⟨st', h, hR⟩ := exists_exec_loop_eq_some_of_forall I (fun _ (s : St P K C) =>
    s.store.shape = st.store.shape ∧
      ∀ q b j, b ≠ Y → s.store.read q b j = st.store.read q b j) ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun w hw s ⟨hs, hf⟩ => by
      obtain ⟨s', h', hs', hf'⟩ := hstep w hw s hs hf
      exact ⟨s', h', hs'.trans hs, fun q b j hb => (hf' q b j hb).trans (hf q b j hb)⟩) (st := st)
  exact ⟨st', h, hR⟩

/-- EL2: a leaf succeeds when its blocks are allocated and its matrix is stored. -/
private theorem el2_leaf_ex {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (diag : Bool) (k : ℕ)
    {Ma Ua Ea : ℕ} {mo uo eo : IExp ℕ} {kd : Cell ℕ ℕ} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {lU lE lK : ℕ}
    (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (hUa : st.store.shape[Ua]? = some (p, lU)) (hU : uo.eval + 2 * (k * k) ≤ lU)
    (hEa : st.store.shape[Ea]? = some (p, lE)) (hE : eo.eval + k ≤ lE)
    (hKd : st.store.shape[kd.buf]? = some (p, lK)) (hK : kd.idx.eval < lK)
    (hMaUa : Ma ≠ Ua) (hMaEa : Ma ≠ Ea) :
    ∃ st', exec I (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd).run st =
      some st' := by
  have hii : ∀ i < k, 2 * (i + k * i) + 2 ≤ 2 * (k * k) := fun i hi => by nlinarith
  have hz0 := hsem.lit_ok p 0 trivial
  have hz1 := hsem.lit_ok p 1 trivial
  obtain ⟨z1', hz1'⟩ := hsem.lit_ok p ((1 : ℕ) : ℚ) trivial
  obtain ⟨s1, h1, sh1, fr1⟩ := el2_loop (Y := Ua) (st := st) (m := 2 * (IExp.const k * IExp.const k))
    (body := fun w => .seq (.instr (.lit p ⟨Ua, uo + .var w⟩ 0)) .skip)
    (fun w hw s hs _ => el2_body_lit hz0 (by rw [hs]; exact hUa) (by
      change uo.eval + w < lU
      change w < 2 * (k * k) at hw
      omega))
  obtain ⟨s2, h2, sh2, fr2⟩ := el2_loop (Y := Ua) (st := s1) (m := IExp.const k)
    (body := fun i => .seq (.instr (.lit p ⟨Ua, uo + zidx (.const k) (.var i) (.var i)⟩ 1)) .skip)
    (fun i hi s hs _ => el2_body_lit hz1 (by rw [hs, sh1]; exact hUa) (by
      change uo.eval + 2 * (i + k * i) < lU
      change i < k at hi
      have := hii i hi
      omega))
  have hMa2 : ∀ i < k, ∃ v, s2.store.read p Ma (mo.eval + 2 * (i + k * i)) = some v := by
    intro i hi
    rw [fr2 _ _ _ hMaUa, fr1 _ _ _ hMaUa]
    exact ⟨_, hA ⟨i, hi⟩ ⟨i, hi⟩ ⟨0, two_pos⟩⟩
  obtain ⟨s3, h3, sh3, fr3⟩ := el2_loop (Y := Ea) (st := s2) (m := IExp.const k)
    (body := fun i => ((if diag then Builder.ins (ι := ι) (.copy p ⟨Ea, eo + .var i⟩
        ⟨Ma, mo + zidx (.const k) (.var i) (.var i)⟩)
      else Builder.ins (.lit p ⟨Ea, eo + .var i⟩ 0)) : Builder P ι ℕ ℕ Unit).run)
    (fun i hi s hs hf => by
      change i < k at hi
      cases diag
      · exact el2_body_lit hz0 (by rw [hs, sh2, sh1]; exact hEa) (by change eo.eval + i < lE; omega)
      · refine el2_body_copy ?_ (by rw [hs, sh2, sh1]; exact hEa) (by
          change eo.eval + i < lE; omega)
        obtain ⟨v, hv⟩ := hMa2 i hi
        exact ⟨v, (hf _ _ _ hMaEa).trans hv⟩)
  obtain ⟨s4, hw4⟩ := Store.exists_write_eq_some_of_getElem?_shape z1'
    (by rw [sh3, sh2, sh1]; exact hKd) hK
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) .skip)))
    (.seq (.loop _ _) (.seq (.instr (.litIdx p kd 1)) .skip))) st = some st'
  refine el2_ex_seq (s₁ := s2) ?_ (el2_ex_seq h3
    ⟨_, (exec_seq_instr_litIdx I (v := z1') hz1' hw4).trans (exec_skip I _)⟩)
  rw [exec_named]
  exact (exec_seq_of_exec_eq_some I h1).trans ((exec_seq_of_exec_eq_some I h2).trans
    (exec_skip I _))

/-- EL2: the windows of the levels decode to positive values from a positive $R_0$ and to $0$
from a zero $R_0$. -/
private theorem el2_lp {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (hlit : IsExactIntLit dec I.sem 2) {R₀ ε : K} {ℓ₀ : ℕ} (hℓ : 1 ≤ ℓ₀) :
    ∀ d, (0 < dec p R₀ → 0 < dec p (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1) ∧
      (dec p R₀ = 0 → dec p (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1 = 0) := by
  have hpos : ∀ {δ : ℝ}, |δ| ≤ u p → 0 < 1 + δ := fun h => by
    have := (abs_le.mp h).1; linarith
  obtain ⟨one, hone, hone'⟩ := hlit p 1 (by omega)
  obtain ⟨two, htwo, htwo'⟩ := hlit p 2 (by omega)
  simp only [Nat.cast_one] at hone hone'
  push_cast at htwo'
  intro d
  induction d with
  | zero => exact ⟨id, id⟩
  | succ d ih =>
    obtain ⟨L, hL⟩ := hsem.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) trivial
    obtain ⟨δL, hδL, hLd⟩ := hsem.lit_err p _ L hL
    have hLpos : 0 < dec p L := by
      rw [hLd]
      have hx : (0 : ℝ) < (((ℓ₀ + d : ℕ) : ℚ) : ℝ) := by
        exact_mod_cast (show 0 < ℓ₀ + d by omega)
      exact mul_pos hx (hpos hδL)
    obtain ⟨h1, hh1, δ1, hδ1, hd1⟩ := el2_bin hsem p (b := .div) trivial (x := one) (y := two)
      (fun _ => by rw [htwo']; norm_num)
    obtain ⟨h2, hh2, δ2, hδ2, hd2⟩ := el2_bin hsem p (b := .div) trivial (x := two) (y := L)
      (fun _ => ne_of_gt hLpos)
    obtain ⟨h3, hh3, δ3, hδ3, hd3⟩ := el2_bin hsem p (b := .add) trivial (x := h1) (y := h2)
      (fun h => by cases h)
    obtain ⟨h4, hh4, δ4, hδ4, hd4⟩ := el2_bin hsem p (b := .mul) trivial (x := h3)
      (y := (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1) (fun h => by cases h)
    have e : (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).1 = h4 := by
      change (I.sem.bin p .mul ((I.sem.bin p .add ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default) ((I.sem.bin p .div
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default) ((I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD
        default)).getD default)).getD default) _).getD default = h4
      rw [hone, htwo, hL]
      simp only [Option.getD_some]
      rw [hh1, Option.getD_some, hh2, Option.getD_some, hh3, Option.getD_some, hh4,
        Option.getD_some]
    have hX : 0 < dec p h3 := by
      simp only [BinOp.realOp] at hd1 hd2 hd3
      rw [hd3, hd1, hd2, hone', htwo']
      have := hpos hδ1; have := hpos hδ2; have := hpos hδ3
      have : 0 < 2 / dec p L := by positivity
      positivity
    simp only [BinOp.realOp] at hd4
    rw [e, hd4]
    have := hpos hδ4
    exact ⟨fun h => by have := ih.1 h; positivity, fun h => by rw [ih.2 h]; ring⟩

/-- EL2: the semantics decides flags. -/
private theorem el2_flags {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) {B : ℕ}
    (hlit : IsExactIntLit dec I.sem B) (hB : 1 ≤ B) (p : P) : I.sem.DecidesFlags p := by
  obtain ⟨z, hz, hzd⟩ := hlit p 0 (by omega)
  obtain ⟨o, ho, hod⟩ := hlit p 1 hB
  simp only [Nat.cast_zero, Nat.cast_one] at hz hzd ho hod
  refine ⟨z, o, hz, ho, ?_, ?_⟩
  · rw [hsem.cmp_eq, hzd, hod]; simp
  · rw [hsem.cmp_eq]; simp

omit [Inhabited K] in
/-- EL2: a slot that starts no node succeeds. -/
private theorem el2_slot_skip_ex {p : P} {mm qr : ι}
    {n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo : ℕ} {s : St P K C}
    (hSz : ReadsIdx I.sem s.store p Sz (n * d + lo) 0) :
    ∃ s', exec I (el1_slotBody p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo).run s =
      some s' := by
  unfold el1_slotBody
  refine el2_ex_bindIdx (k := 0) (by exact hSz) (Nat.zero_le _) ?_
  exact ⟨_, el2_when0_eq (by change 1 - (1 - 0) = 0; omega)⟩

set_option maxHeartbeats 1600000 in
-- The slot unfolds the binder, two guards, the window test and the node step.
/-- EL2: the slot of a node of depth $d$ succeeds; a node step's window is positive since its
window test failed. -/
private theorem el2_slot_node_ex {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hℓ : 1 ≤ ℓ₀ + d) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c t lo : ℕ} {s : St P K C}
    {R₀ β : K} {y : EighNode K} (hk1 : 1 ≤ y.k) (hkn : lo + y.k ≤ n)
    (hH : H.Shaped s.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (ht : t ∉ H.handles ++ [par, c]) (ht4 : ∃ len, s.store.shape[t]? = some (p, len) ∧ 4 < len)
    (hSz : ReadsIdx I.sem s.store p H.Sz (n * d + lo) y.k)
    (hA : pairLayout.Holds s.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A)
    (hR : s.store.read p H.Lv (2 * d) = some y.R) (hR₀ : 0 ≤ dec p R₀)
    (hRpos : 0 < dec p R₀ → 0 < dec p y.R) (hRz : dec p R₀ = 0 → dec p y.R = 0)
    (hε : s.store.read p H.Lv (2 * d + 1) = some y.ε)
    (hpar : s.store.read p par 0 = some R₀ ∧ s.store.read p par 2 = some β)
    (hSu : 2 ≤ y.k → (∃ v, s.store.read p Su lo = some v) ∧ (Su = t → lo ≠ 4))
    (hSg : 2 ≤ y.k → (∀ w < 4 * (n * n), ∃ v, s.store.read p Sg w = some v) ∧ Sg ≠ t)
    (hc : s.store.read p c 0 = I.sem.lit p 1 ∧ s.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      (∃ v, s.store.read p c 2 = some v) ∧ (∃ v, s.store.read p c 3 = some v) ∧
      s.store.read p c 4 = some (I.sem.sqrtHalf p)) :
    ∃ s', exec I (el1_slotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c t lo).run s = some s' := by
  have dUaMa : H.Ua ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dEaMa : H.Ea ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dtLv : H.Lv ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtMa : H.Ma ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtpar : par ≠ t := fun h => ht (by simp [h])
  have dtc : c ≠ t := fun h => ht (by simp [h])
  obtain ⟨-, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
  have e5 : 2 * n * lo + 2 * (n * y.k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) hkn
    nlinarith
  have e6 : 2 * (n * n) * d + 2 * (n * n) ≤ 2 * (n * n) * (D + 1) := by
    have := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ D + 1 by omega)
    nlinarith
  have e7 : n * d + n ≤ n * D := by
    have := Nat.mul_le_mul_left n (show d + 1 ≤ D by omega)
    nlinarith
  have e8 : n * D ≤ n * (D + 1) := Nat.mul_le_mul_left n (by omega)
  -- a leaf, from a state with the shape of `s` and the node's matrix stored
  have hleaf : ∀ (diag : Bool) (σ : St P K C), σ.store.shape = s.store.shape →
      pairLayout.Holds σ.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A →
      ∃ σ', exec I (eighLeafBlock (ι := ι) p diag (.var y.k) H.Ma
        (eighBlockOff (.const n) (.const d) (.var lo)) H.Ua
        (eighBlockOff (.const n) (.const d) (.var lo)) H.Ea
        (eighSlotOff (.const n) (.const d) (.var lo))
        ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩).run σ = some σ' := by
    intro diag σ hσ hAσ
    obtain ⟨σ', h'⟩ := el2_leaf_ex hsem p diag y.k (A := y.A) (st := σ) (Ma := H.Ma)
      (Ua := H.Ua) (Ea := H.Ea) (mo := eighBlockOff (.const n) (.const d) (.var lo))
      (uo := eighBlockOff (.const n) (.const d) (.var lo))
      (eo := eighSlotOff (.const n) (.const d) (.var lo))
      (kd := ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) (by exact hAσ)
      (by rw [hσ]; exact hUa) (by change 2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ _; omega)
      (by rw [hσ]; exact hEa) (by change n * d + lo + y.k ≤ _; omega)
      (by rw [hσ]; exact hKd) (by change n * d + lo < _; omega)
      (fun h => dUaMa h.symm) (fun h => dEaMa h.symm)
    exact ⟨σ', (el1_leaf_congr p diag y.k H.Ma H.Ua H.Ea _ _ _ _ _).trans h'⟩
  unfold el1_slotBody
  refine el2_ex_bindIdx (k := y.k) (by exact hSz) (by change y.k ≤ n - lo; omega) ?_
  refine el2_ex_when1 (by change 1 - (1 - y.k) = 1; omega) ?_
  rcases Nat.lt_or_ge y.k 2 with hk | hk
  · obtain ⟨σ', h'⟩ := hleaf true { s with cnt := s.cnt + I.charge (.toNat p) } rfl hA
    refine el2_ex_whenBind (σ := σ') ?_ ?_
    · exact (el2_when1_eq (e := 1 - (1 - (1 - (IExp.var y.k - 1))))
        (by change 1 - (1 - (1 - (y.k - 1))) = 1; omega)).trans h'
    · exact ⟨_, el2_when0_eq (by change 1 - (1 - (y.k - 1)) = 0; omega)⟩
  · refine el2_ex_whenBind (el2_when0_eq (by change 1 - (1 - (1 - (y.k - 1))) = 0; omega)) ?_
    refine el2_ex_when1 (by change 1 - (1 - (y.k - 1)) = 1; omega) ?_
    obtain ⟨len, htsh, hlen⟩ := ht4
    obtain ⟨v, hv, δ, hδ, hvd⟩ := el2_bin hsem p (b := .mul) trivial (x := y.ε) (y := R₀)
      (fun h => by cases h)
    obtain ⟨s₂, hw2⟩ := Store.exists_write_eq_some_of_getElem?_shape v htsh hlen
    have hr2 : ∀ q b i, ¬ (b = t ∧ i = 4) → s₂.read q b i = s.store.read q b i :=
      fun q b i hne => Store.read_of_write_eq_some_of_ne hw2 (not_and_or.mp hne)
    have hsh2 : s₂.shape = s.store.shape := Store.shape_of_write_eq_some hw2
    have hA2 : pairLayout.Holds s₂ p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A :=
      el1_holds_keep hA fun i _ _ => hr2 _ _ _ fun h => dtMa h.1
    refine el2_ex_bin (s' := s₂) (by exact hε) (by exact hpar.1) hv (by exact hw2) ?_
    change ∃ st', exec I (.seq (.ite _ _ _ _ _ _) .skip) _ = some st'
    refine el2_ex_ite (a := y.R) (b := v) (by exact (hr2 _ _ _ fun h => dtLv h.1).trans hR)
      (by exact Store.read_of_write_eq_some hw2) (hsem.cmp_le p y.R v) ?_
    by_cases hle : dec p y.R ≤ dec p v
    · rw [if_pos (decide_eq_true hle)]
      exact hleaf false _ hsh2 hA2
    · rw [if_neg (by simpa using hle)]
      have hRp : 0 < dec p y.R := by
        rcases hR₀.lt_or_eq with h | h
        · exact hRpos h
        · exfalso
          apply hle
          rw [hRz h.symm, hvd, ← h]
          simp [BinOp.realOp]
      obtain ⟨hSu1, hSu2⟩ := hSu hk
      obtain ⟨hSg1, hSg2⟩ := hSg hk
      obtain ⟨sN, hN⟩ := exists_exec_eighNodeBlock hmm hqr hsem
        (fun p k hk => hlit p k (by omega)) htn p hu n ℓ₀ F d lo y.k
        (fun p k hk => hlit p k (by omega)) hkn hk hℓ H (A := y.A)
        (R := y.R) (β := β) (st := { s with store := s₂, cnt := _ }) hd
        (el1_shaped_of_eq (fun b _ => by change s₂.shape[b]? = _; rw [hsh2]) hH) hbufs hA2
        ((hr2 _ _ _ fun h => dtLv h.1).trans hR) hRp
        ((hr2 _ _ _ fun h => dtpar h.1).trans hpar.2)
        (by obtain ⟨w, hw⟩ := hSu1; exact ⟨w, (hr2 _ _ _ fun h => hSu2 h.1 h.2).trans hw⟩)
        (fun w hw => by
          obtain ⟨x, hx⟩ := hSg1 w hw
          exact ⟨x, (hr2 _ _ _ fun h => hSg2 h.1).trans hx⟩)
        ⟨(hr2 _ _ _ fun h => dtc h.1).trans hc.1, (hr2 _ _ _ fun h => dtc h.1).trans hc.2.1,
          by obtain ⟨x, hx⟩ := hc.2.2.1; exact ⟨x, (hr2 _ _ _ fun h => dtc h.1).trans hx⟩,
          by obtain ⟨x, hx⟩ := hc.2.2.2.1; exact ⟨x, (hr2 _ _ _ fun h => dtc h.1).trans hx⟩,
          (hr2 _ _ _ fun h => dtc h.1).trans hc.2.2.2.2⟩
      exact ⟨sN, (el1_node_congr p mm qr n ℓ₀ F d lo y.k par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp c
        _).trans hN⟩

set_option maxHeartbeats 1600000 in
-- The run unfolds the scope, seven instructions, two draw loops and the loop over the slots.
/-- **One level of the downward pass succeeds** under the standard model at $u$ with every value in
range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor conversion, if the
kernels are routines on pairs, $\ell_0 \ge 1$, $\varepsilon$ and $R_0$ decode to nonnegative values
and the arenas hold the nodes of depth $d$ (hypotheses as `NLAlib.holds_of_exec_eighDownLevel`, with
its tape positions and constants). No printed source.
Proof: the parameters (divisions by $\mathrm{fl}(\ell) \ne 0$, `lit_err`, $u(p) < 1$), the draws,
and the loop over the slots by `NLAlib.Computation.exists_exec_loop_eq_some_of_forall` with the
invariant of `NLAlib.holds_of_exec_eighDownLevel`: each binder succeeds (`htn`), each leaf
(`lit_ok`, copies of initialised cells), and each node by `NLAlib.exists_exec_eighNodeBlock`, whose
window is positive: the comparison $R \le \mathrm{fl}(\varepsilon R_0)$ failed and
$\mathrm{fl}(\varepsilon R_0)$ decodes to $\bar\varepsilon\bar R_0(1 + \delta) \ge 0$ (`bin_err`,
`cmp_le`). L, about 120 lines. -/
theorem exists_exec_eighDownLevel {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hℓ : 1 ≤ ℓ₀) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hSu : ∃ len, st.store.shape[Su]? = some (p, len) ∧ n ≤ len)
    (hSg : ∃ len, st.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su
      Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st = some st' := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hlev1, hlev2, hlev3, hlev4⟩ := hlev
  set tH := st.store.size with htH
  set S0 : Store P K := st.store.push (p, Array.replicate (5 : IExp ℕ).eval none) with hS0
  have hflag : I.sem.DecidesFlags p := el2_flags hsem hlit (by omega) p
  have hcmp := hsem.cmp_le p
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  obtain ⟨z0, o1, -, hl1, -, -⟩ := id hflag
  have lpar := Store.lt_size_of_read_eq_some hpar.1
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans hl1)
  have lMa := hsz hMa
  have lUa := hsz hUa
  have lQa := hsz hQa
  have lEa := hsz hEa
  have lSz := hsz hSzs
  have lKd := hsz hKd
  have lKp := hsz hKp
  have lLv := hsz hLv
  have dLvc : H.Lv ≠ c := fun h => by simp [EighArenas.handles, h] at hbufs
  have dLvSu : H.Lv ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dLvSg : H.Lv ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzSu : H.Sz ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzSg : H.Sz ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzLv : H.Sz ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSu : H.Ma ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSg : H.Ma ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaLv : H.Ma ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSu : par ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSg : par ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparLv : par ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSu : c ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSg : c ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSuSg : Su ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have hpb : par ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hcb : c ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hSub : Su ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hSgb : Sg ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hLvb : H.Lv ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hnd
  have hwinb : ∀ {lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}, el1_win H n d lo k cs b i →
      b < st.store.size := fun hw => by
    have := el1_win_buf hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hr0 : ∀ q b i, b < tH → S0.read q b i = st.store.read q b i :=
    fun q b i hb => Store.read_push_of_lt hb
  have dcT : c ≠ tH := by omega
  have dLvT : H.Lv ≠ tH := by omega
  have hS0sz : S0.size = tH + 1 := by rw [hS0, Array.size_push, htH]
  have hshape5 : S0.shape[tH]? = some (p, 5) := Store.getElem?_shape_push_size _ _ _
  have hLvsh : S0.shape[H.Lv]? = some (p, 2 * (D + 1)) := by
    rw [hS0, Store.getElem?_shape_push_of_lt _ lLv]; exact hLv
  have hpos1 : ∀ {δ : ℝ}, |δ| ≤ u p → 0 < 1 + δ := fun h => by
    have := (abs_le.mp h).1; linarith
  -- the values of the seven instructions
  obtain ⟨tw, htw, -⟩ := hlit p 2 (by omega)
  obtain ⟨v0, hv0'⟩ := hsem.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) trivial
  have hv0pos : 0 < dec p v0 := by
    obtain ⟨δ, hδ, hvd⟩ := hsem.lit_err p _ v0 hv0'
    rw [hvd]
    have hx : (0 : ℝ) < (((ℓ₀ + d : ℕ) : ℚ) : ℝ) := by
      exact_mod_cast (show 0 < ℓ₀ + d by omega)
    exact mul_pos hx (hpos1 hδ)
  obtain ⟨v1, hv1, -⟩ := el2_bin hsem p (b := .div) trivial (x := tw) (y := v0)
    (fun _ => ne_of_gt hv0pos)
  obtain ⟨v2, hv2, -⟩ := el2_bin hsem p (b := .add) trivial (x := M.div M.one (M.ofNat 2))
    (y := v1) (fun h => by cases h)
  obtain ⟨v3, hv3, -⟩ := el2_bin hsem p (b := .mul) trivial (x := v2)
    (y := (eighLevelParams M R₀ ε ℓ₀ d).1) (fun h => by cases h)
  obtain ⟨v4, hv4, -⟩ := el2_bin hsem p (b := .div) trivial (x := o1) (y := v0)
    (fun _ => ne_of_gt hv0pos)
  obtain ⟨v5, hv5, -⟩ := el2_bin hsem p (b := .sub) trivial (x := o1) (y := v4)
    (fun h => by cases h)
  obtain ⟨v6, hv6, -⟩ := el2_bin hsem p (b := .mul) trivial (x := v5)
    (y := (eighLevelParams M R₀ ε ℓ₀ d).2) (fun h => by cases h)
  obtain ⟨S1, hw0'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) v0 hshape5
    (by norm_num)
  have sh1 : S1.shape = S0.shape := Store.shape_of_write_eq_some hw0'
  obtain ⟨S2, hw1'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2) v1
    (by rw [sh1]; exact hshape5) (by norm_num)
  have sh2 : S2.shape = S0.shape := (Store.shape_of_write_eq_some hw1').trans sh1
  obtain ⟨S3, hw2'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 3) v2
    (by rw [sh2]; exact hshape5) (by norm_num)
  have sh3 : S3.shape = S0.shape := (Store.shape_of_write_eq_some hw2').trans sh2
  obtain ⟨S4, hw3'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2 * (d + 1)) v3
    (by rw [sh3]; exact hLvsh) (by omega)
  have sh4 : S4.shape = S0.shape := (Store.shape_of_write_eq_some hw3').trans sh3
  obtain ⟨S5, hw4'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) v4
    (by rw [sh4]; exact hshape5) (by norm_num)
  have sh5 : S5.shape = S0.shape := (Store.shape_of_write_eq_some hw4').trans sh4
  obtain ⟨S6, hw5'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 3) v5
    (by rw [sh5]; exact hshape5) (by norm_num)
  have sh6 : S6.shape = S0.shape := (Store.shape_of_write_eq_some hw5').trans sh5
  obtain ⟨S7, hw6'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2 * (d + 1) + 1) v6
    (by rw [sh6]; exact hLvsh) (by omega)
  -- the reads of the seven instructions
  have ea1 : S1.read p c 1 = st.store.read p c 1 := by
    rw [Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have ea2 : S2.read p c 2 = st.store.read p c 2 := by
    rw [Store.read_of_write_eq_some_of_ne hw1' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have eb3 : S3.read p H.Lv (2 * d) = st.store.read p H.Lv (2 * d) := by
    rw [Store.read_of_write_eq_some_of_ne hw2' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dLvT), hr0 _ _ _ lLv]
  have ea4 : S4.read p c 0 = st.store.read p c 0 := by
    rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inl dLvc.symm),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have eb4 : S4.read p tH 0 = some v0 := by
    rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inl dLvT.symm),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inr (by omega)),
      Store.read_of_write_eq_some hw0']
  have ea5 : S5.read p c 0 = st.store.read p c 0 := by
    rw [Store.read_of_write_eq_some_of_ne hw4' (Or.inl dcT), ea4]
  have eb6 : S6.read p H.Lv (2 * d + 1) = st.store.read p H.Lv (2 * d + 1) := by
    rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dLvT), hr0 _ _ _ lLv]
  have r1a : S1.read p c 1 = some tw := ea1.trans (hc.2.1.trans htw)
  have r1b : S1.read p tH 0 = some v0 := Store.read_of_write_eq_some hw0'
  have r2a : S2.read p c 2 = some (M.div M.one (M.ofNat 2)) := ea2.trans hc.2.2.1
  have r2b : S2.read p tH 2 = some v1 := Store.read_of_write_eq_some hw1'
  have r3a : S3.read p tH 3 = some v2 := Store.read_of_write_eq_some hw2'
  have r3b : S3.read p H.Lv (2 * d) = some (eighLevelParams M R₀ ε ℓ₀ d).1 := eb3.trans hlev3
  have r4a : S4.read p c 0 = some o1 := ea4.trans (hc.1.trans hl1)
  have r5a : S5.read p c 0 = some o1 := ea5.trans (hc.1.trans hl1)
  have r5b : S5.read p tH 1 = some v4 := Store.read_of_write_eq_some hw4'
  have r6a : S6.read p tH 3 = some v5 := Store.read_of_write_eq_some hw5'
  have r6b : S6.read p H.Lv (2 * d + 1) = some (eighLevelParams M R₀ ε ℓ₀ d).2 :=
    eb6.trans hlev4
  -- the frame of the seven instructions
  have hr7 : ∀ q b i, b < tH → ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      S7.read q b i = st.store.read q b i := by
    intro q b i hb hL
    have hbT : b ≠ tH := by omega
    have hL' : b ≠ H.Lv ∨ (i ≠ 2 * (d + 1) ∧ i ≠ 2 * (d + 1) + 1) := by
      by_cases h' : b = H.Lv
      · exact Or.inr ⟨fun h'' => hL ⟨h', Or.inl h''⟩, fun h'' => hL ⟨h', Or.inr h''⟩⟩
      · exact Or.inl h'
    rw [Store.read_of_write_eq_some_of_ne hw6' (hL'.imp_right And.right),
      Store.read_of_write_eq_some_of_ne hw5' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw3' (hL'.imp_right And.left),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl hbT), hr0 _ _ _ hb]
  have hsh7 : S7.shape = S0.shape := by
    rw [Store.shape_of_write_eq_some hw6', Store.shape_of_write_eq_some hw5',
      Store.shape_of_write_eq_some hw4', Store.shape_of_write_eq_some hw3',
      Store.shape_of_write_eq_some hw2', Store.shape_of_write_eq_some hw1',
      Store.shape_of_write_eq_some hw0']
  -- the run of the parameters
  change ∃ st', exec I (.seq (.alloc p _ _) .skip) st = some st'
  rw [exec_seq_skip, exec_alloc]
  refine el2_map_ex ?_
  refine el2_ex_litIdx (by exact hv0') (by exact hw0') ?_
  refine el2_ex_bin (by exact r1a) (by exact r1b) hv1 (by exact hw1') ?_
  refine el2_ex_bin (by exact r2a) (by exact r2b) hv2 (by exact hw2') ?_
  refine el2_ex_bin (by exact r3a) (by exact r3b) hv3 (by exact hw3') ?_
  refine el2_ex_bin (by exact r4a) (by exact eb4) hv4 (by exact hw4') ?_
  refine el2_ex_bin (by exact r5a) (by exact r5b) hv5 (by exact hw5') ?_
  refine el2_ex_bin (by exact r6a) (by exact r6b) hv6 (by exact hw6') ?_
  refine el2_name fun σ7 hσ7 => ?_
  have h7s : σ7.store = S7 := by rw [hσ7]
  have h7p : σ7.pos = st.pos := by rw [hσ7]
  -- the draws
  obtain ⟨len1, hSush, hlen1⟩ := hSu
  obtain ⟨len2, hSgsh, hlen2⟩ := hSg
  have lSu : Su < tH := hsz hSush
  have lSg : Sg < tH := hsz hSgsh
  have hS7Su : S7.shape[Su]? = some (p, len1) := by
    rw [hsh7, hS0, Store.getElem?_shape_push_of_lt _ lSu]; exact hSush
  have hS7Sg : S7.shape[Sg]? = some (p, len2) := by
    rw [hsh7, hS0, Store.getElem?_shape_push_of_lt _ lSg]; exact hSgsh
  obtain ⟨σu, hdu, -⟩ := exec_forRange_draw I p .uniform Su 0 (.const n) (fun i => .var i)
    (fun i => (Nat.zero_add i).symm) σ7 (fun i hi => ⟨_,
      Store.exists_write_eq_some_of_getElem?_shape (I.tape .uniform 0) (by rw [h7s]; exact hS7Su)
        (by change i < n at hi; omega)⟩)
  have hu' : exec I (.loop (.const n) fun i =>
      (Builder.ins (ι := ι) (.draw p .uniform ⟨Su, .var i⟩)).run) σ7 = some σu :=
    (exec_seq_skip I _ _).symm.trans hdu
  refine el2_ex_seq hu' ?_
  obtain ⟨hush, hupos, hurd, hufr⟩ := el1_draw_loop hu'
  obtain ⟨σg, hg, -⟩ := exec_forRange_draw I p .gaussian Sg 0 (4 * (IExp.const n * IExp.const n))
    (fun w => .var w) (fun w => (Nat.zero_add w).symm) σu (fun w hw => ⟨_,
      Store.exists_write_eq_some_of_getElem?_shape (I.tape .gaussian 0)
        (by rw [hush, h7s]; exact hS7Sg) (by change w < 4 * (n * n) at hw; omega)⟩)
  have hg' : exec I (.loop (4 * (IExp.const n * IExp.const n)) fun w =>
      (Builder.ins (ι := ι) (.draw p .gaussian ⟨Sg, .var w⟩)).run) σu = some σg :=
    (exec_seq_skip I _ _).symm.trans hg
  refine el2_ex_seq hg' ?_
  obtain ⟨hgsh, hgpos, hgrd, hgfr⟩ := el1_draw_loop hg'
  have hshg : σg.store.shape = S0.shape := by rw [hgsh, hush, h7s, hsh7]
  have hSuR : ∀ w < n, σg.store.read p Su w = some (I.tape .uniform (n * d + w)) := by
    intro w hw
    rw [hgfr _ _ _ (Or.inl dSuSg), hurd w hw, h7p, hpos.1]
  have hSgR : ∀ w < 4 * (n * n), σg.store.read p Sg w =
      some (I.tape .gaussian (4 * (n * n) * d + w)) := by
    intro w hw
    rw [hgrd w hw, hupos]
    simp [h7p, hpos.2]
  have hrg : ∀ q b i, b < tH → b ≠ Su → b ≠ Sg →
      ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      σg.store.read q b i = st.store.read q b i := fun q b i hb h1 h2 h3 => by
    rw [hgfr _ _ _ (Or.inl h2), hufr _ _ _ (Or.inl h1), h7s]
    exact hr7 q b i hb h3
  have hSut : Su = tH → 1 ≤ n → n ≤ 5 := by
    intro hS hn
    obtain ⟨len, hlen, hi⟩ := Store.exists_getElem?_shape_of_read_eq_some (hSuR (n - 1) (by omega))
    rw [hshg, hS, hshape5, Option.some.injEq, Prod.mk.injEq] at hlen
    omega
  have hSgt : Sg = tH → 1 ≤ n → 4 * (n * n) ≤ 5 := by
    intro hS hn
    have hn2 : 0 < 4 * (n * n) := by positivity
    obtain ⟨len, hlen, hi⟩ :=
      Store.exists_getElem?_shape_of_read_eq_some (hSgR (4 * (n * n) - 1) (by omega))
    rw [hshg, hS, hshape5, Option.some.injEq, Prod.mk.injEq] at hlen
    omega
  have hH0 : H.Shaped σg.store p n D :=
    el1_shaped_of_eq (fun b hb => by
      rw [hshg, hS0, Store.getElem?_shape_push_of_lt _ (by
        simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)]) hH
  have htb : tH ∉ H.handles ++ [par, c] := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    omega
  have hnd' : H.handles.Nodup := hnd
  -- nodes of depth d: bounds and uniqueness
  have hbnd : ∀ {a : List Bool} {lo : ℕ} {y : EighNode K},
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) → 1 ≤ y.k →
        1 ≤ n ∧ lo + y.k ≤ n := by
    intro a lo y hl hk
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      cases a with
      | nil =>
        simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨-, rfl⟩ := hl
        exact absurd hk (by simp [hn])
      | cons b a =>
        have h0 : n ≤ 1 := by omega
        simp [eighLoc, eighStep, h0] at hl
    · exact ⟨hn, (eighLoc_bounds hn hl).2⟩
  have huniq : ∀ {a a' : List Bool} {lo : ℕ} {y y' : EighNode K}, a.length = d →
      a'.length = d → eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) →
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo, y') → 1 ≤ n → y = y' := by
    intro a a' lo y y' ha ha' hl hl' hn
    by_cases hae : a = a'
    · subst hae
      rw [hl] at hl'
      simp only [Option.some.injEq, Prod.mk.injEq] at hl'
      exact hl'.2
    · have h1 := (eighLoc_bounds hn hl).1
      have h2 := (eighLoc_bounds hn hl').1
      rcases eighLoc_disjoint (ha.trans ha'.symm) hae hl hl' with h | h <;> omega
  have hlp := el2_lp (mmR := mmR) (qrR := qrR) hsem p hu (fun p k hk => hlit p k (by omega))
    (R₀ := R₀) (ε := ε) hℓ d
  -- the loop over the slots
  have hex := exists_exec_loop_eq_some_of_forall I (n := .const n)
    (body := fun lo => (el1_slotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz
      H.Kd H.Kp c tH lo).run) (st := σg) (fun w (s : St P K C) =>
      s.store.shape = σg.store.shape ∧ s.pos = σg.pos ∧
      (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
        el1_done H I.sem s.store p M n F d R₀ β lo y) ∧
      ∀ q b i, (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
          ¬ el1_win H n d lo y.k (el1_childSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ
            (eighTapeSample n d lo)) lo) b i) → ¬ (b = tH ∧ i = 4) →
        s.store.read q b i = σg.store.read q b i)
    ⟨rfl, rfl, fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl⟩ ?_
  swap
  · rintro w hw s₁ ⟨hsh1, hps1, hdn1, hfr1⟩
    change w < n at hw
    have hn1 : 1 ≤ n := by omega
    have hrd1 : ∀ q b i, b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] → ¬ (b = tH ∧ i = 4) →
        s₁.store.read q b i = σg.store.read q b i :=
      fun q b i hb ht => hfr1 q b i (fun _ _ _ _ => el1_not_win_buf hb) ht
    have hSz1 : ∀ i, i < n * (d + 1) → s₁.store.read p H.Sz i = st.store.read p H.Sz i :=
      fun i hi => (hfr1 _ _ _ (fun _ _ _ _ => el1_not_win_Sz hnd' hi) (fun h => by omega)).trans
        (hrg _ _ _ lSz dSzSu dSzSg fun h => dSzLv h.1)
    have he4 : (n * (d + 1)) = n * d + n := by ring
    by_cases hnode : ∃ (y : EighNode K) (a : List Bool), a.length = d ∧
        eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y)
    · obtain ⟨y, a, ha, hl⟩ := hnode
      obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn1 hl
      obtain ⟨hyR, hyε, hyℓ⟩ := eighLoc_params hl
      rw [ha] at hyR hyε hyℓ
      have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
      have e5 : 2 * n * w + 2 * (n * y.k) ≤ 2 * (n * n) := by
        have := Nat.mul_le_mul_left (2 * n) hkn
        nlinarith
      have e6 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
      have ish : H.Shaped s₁.store p n D := el1_shaped_of_eq (fun b _ => by rw [hsh1]) hH0
      have iSz := el1_readsIdx_congr (hSz1 _ (by omega)) (hlev1 a w y ha hl).1
      have iA : pairLayout.Holds s₁.store p H.Ma (2 * (n * n) * d + 2 * n * w) y.A :=
        el1_holds_keep (hlev1 a w y ha hl).2 fun i h1 h2 =>
          (hfr1 _ _ _ (fun _ _ _ _ => el1_not_win_Ma hnd' (by omega)) (fun h => by omega)).trans
            (hrg _ _ _ lMa dMaSu dMaSg fun h => dMaLv h.1)
      have iR : s₁.store.read p H.Lv (2 * d) = some y.R := by
        rw [hrd1 p H.Lv (2 * d) hLvb (fun h => by omega),
          hrg p H.Lv (2 * d) lLv dLvSu dLvSg (fun h => by omega)]
        exact hlev3.trans (congrArg some hyR.symm)
      have iε : s₁.store.read p H.Lv (2 * d + 1) = some y.ε := by
        rw [hrd1 p H.Lv (2 * d + 1) hLvb (fun h => by omega),
          hrg p H.Lv (2 * d + 1) lLv dLvSu dLvSg (fun h => by omega)]
        exact hlev4.trans (congrArg some hyε.symm)
      have ipar : s₁.store.read p par 0 = some R₀ ∧ s₁.store.read p par 2 = some β :=
        ⟨by rw [hrd1 p par 0 hpb (fun h => by omega),
              hrg p par 0 lpar dparSu dparSg (fun h => dparLv h.1), hpar.1],
          by rw [hrd1 p par 2 hpb (fun h => by omega),
              hrg p par 2 lpar dparSu dparSg (fun h => dparLv h.1), hpar.2]⟩
      have iSu : 2 ≤ y.k → s₁.store.read p Su w = some (I.tape .uniform (n * d + w)) ∧
          (Su = tH → w ≠ 4) := fun hk2 => by
        have hSu4 : Su = tH → w ≠ 4 := fun hS => by have := hSut hS hn1; omega
        exact ⟨(hrd1 _ _ _ hSub fun h => hSu4 h.1 h.2).trans (hSuR w hw), hSu4⟩
      have iSg : 2 ≤ y.k → (∀ w' < 4 * (n * n), s₁.store.read p Sg w' =
          some (I.tape .gaussian (4 * (n * n) * d + w'))) ∧ Sg ≠ tH := fun hk2 => by
        have hSgT : Sg ≠ tH := fun hS => by
          have := hSgt hS hn1
          have : 2 ≤ n := by omega
          nlinarith
        exact ⟨fun w' hw' => (hrd1 _ _ _ hSgb fun h => hSgT h.1).trans (hSgR w' hw'), hSgT⟩
      have ic : s₁.store.read p c 0 = I.sem.lit p 1 ∧
          s₁.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
          s₁.store.read p c 2 = some (M.div M.one (M.ofNat 2)) ∧
          s₁.store.read p c 3 = some (M.neg M.one) ∧
          s₁.store.read p c 4 = some (I.sem.sqrtHalf p) :=
        ⟨by rw [hrd1 p c 0 hcb (fun h => by omega),
              hrg p c 0 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.1],
          by rw [hrd1 p c 1 hcb (fun h => by omega),
              hrg p c 1 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.1],
          by rw [hrd1 p c 2 hcb (fun h => by omega),
              hrg p c 2 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.1],
          by rw [hrd1 p c 3 hcb (fun h => by omega),
              hrg p c 3 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.2.1],
          by rw [hrd1 p c 4 hcb (fun h => by omega),
              hrg p c 4 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.2.2]⟩
      obtain ⟨s₂, hex⟩ := el2_slot_node_ex hmm hqr hsem p hu n ℓ₀ F d D hd (by omega) hlit htn H
        (par := par) (Su := Su) (Sg := Sg) (c := c) (t := tH) (s := s₁) (R₀ := R₀) (β := β)
        hk1 hkn ish hbufs htb ⟨5, by rw [hsh1, hshg]; exact hshape5, by norm_num⟩ iSz iA iR hR₀
        (fun h => by rw [hyR]; exact (hlp.1 h)) (fun h => by rw [hyR]; exact (hlp.2 h)) iε ipar
        (fun hk2 => ⟨⟨_, (iSu hk2).1⟩, (iSu hk2).2⟩)
        (fun hk2 => ⟨fun w' hw' => ⟨_, (iSg hk2).1 w' hw'⟩, (iSg hk2).2⟩)
        ⟨ic.1, ic.2.1, ⟨_, ic.2.2.1⟩, ⟨_, ic.2.2.2.1⟩, ic.2.2.2.2⟩
      obtain ⟨hdone, hfrW, hsh2, hps2⟩ := el1_slot_node hmm hqr p hflag hcmp n ℓ₀ F d D hd hlit htn
        H
        (par := par) (Su := Su) (Sg := Sg) (c := c) (t := tH) (s := s₁) (s' := s₂) (R₀ := R₀)
        (β := β) hk1 hkn hyℓ ish hbufs htb iSz iA iR iε ipar iSu iSg ic hex
      refine ⟨s₂, hex, hsh2.trans hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
        fun q b i hall ht4 => ?_⟩
      · obtain ⟨a', ha', hl'⟩ := hn'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
        · have hk1' := (eighLoc_bounds hn1 hl').1
          have hkn' := (eighLoc_bounds hn1 hl').2
          have hdis : lo + y'.k ≤ w := by
            have hae : a' ≠ a := fun h => by
              subst h
              rw [hl] at hl'
              have := (Prod.mk.inj (Option.some_inj.mp hl')).1
              omega
            rcases eighLoc_disjoint (ha'.trans ha.symm) hae hl' hl with h | h <;> omega
          exact el1_done_congr hk1' hkn' (fun b i hwin => hfrW p b i
            (fun hw' => el1_win_disjoint hnd' hk1' hdis hwin hw')
            (fun h => by have := hwinb hwin; omega)) (hdn1 lo y' hlo ⟨a', ha', hl'⟩)
        · rw [← huniq ha ha' hl hl' hn1]
          exact hdone
      · rw [hfrW q b i (hall w y (Nat.lt_succ_self w) ⟨a, ha, hl⟩) ht4]
        exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4
    · have hSz0 := hlev2 w hw (fun a y ha hl => hnode ⟨y, a, ha, hl⟩)
      have iSz0 := el1_readsIdx_congr (s' := s₁.store) (hSz1 _ (by omega)) hSz0
      obtain ⟨s₂, hex⟩ := el2_slot_skip_ex (mm := mm) (qr := qr) (n := n) (ℓ₀ := ℓ₀) (F := F)
        (d := d) (par := par) (Lv := H.Lv) (Su := Su) (Sg := Sg) (Ma := H.Ma) (Ua := H.Ua)
        (Qa := H.Qa) (Ea := H.Ea) (Kd := H.Kd) (Kp := H.Kp) (c := c) (t := tH) iSz0
      obtain ⟨hst, hps2⟩ := el1_slot_skip (s := s₁) (s' := s₂) iSz0 hex
      refine ⟨s₂, hex, by rw [hst]; exact hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
        fun q b i hall ht4 => ?_⟩
      · rw [hst]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
        · exact hdn1 lo y' hlo hn'
        · obtain ⟨a', ha', hl'⟩ := hn'
          exact absurd ⟨y', a', ha', hl'⟩ hnode
      · rw [hst]
        exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4
  obtain ⟨σe, he, -⟩ := hex
  exact el2_ex_seq he ⟨σe, exec_skip I σe⟩

omit [Inhabited K] in
/-- A successful loop of literals into the cells `f w` of one buffer keeps the shape and the tape
positions, leaves the literal in every written cell and every other cell unchanged. -/
private theorem read_of_exec_loop_lit {p : P} {m : IExp ℕ} {Y : ℕ} {f : ℕ → IExp ℕ} {c : ℚ}
    {st st' : St P K C}
    (h : exec I (.loop m fun w => .seq (.instr (.lit p ⟨Y, f w⟩ c)) .skip) st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ w < m.eval, ∃ z, I.sem.lit p c = some z ∧ st'.store.read p Y (f w).eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w < m.eval, (f w).eval ≠ i) →
        st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧
      (∀ w' < w, ∃ z, I.sem.lit p c = some z ∧ s.store.read p Y (f w').eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w' < w, (f w').eval ≠ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun w' hw => ?_,
    fun q b i hb => ?_⟩
  · by_cases hww : (f w').eval = (f w).eval
    · exact ⟨v, hv, hww ▸ Store.read_of_write_eq_some hw'⟩
    · have hlt : w' < w := lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) (fun h => hww (h ▸ rfl))
      rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr hww)]
      exact hrd w' hlt
  · rw [Store.read_of_write_eq_some_of_ne hw' ?_]
    · exact hfr q b i (hb.imp_right fun h w' hw => h w' (Nat.lt_succ_of_lt hw))
    · exact hb.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

/-- The run of the spent level at a node of size $k$ at slot $lo$: the stored identity in its
output block, zeros in its eigenvalue cells, every other cell, the shape and the positions kept. -/
private theorem eighBottomLevel_node_run (p : P) (n D lo k : ℕ) (H : EighArenas)
    {s₀ s₂ : St P K C} (hUE : H.Ua ≠ H.Ea)
    (h : exec I (do
        zidentity (ι := ι) p (.var k) H.Ua (eighBlockOff (.const n) (.const D) (.var lo))
        forRange (.var k) fun i =>
          ins (.lit p ⟨H.Ea, eighSlotOff (.const n) (.const D) (.var lo) + IExp.var i⟩ 0)).run s₀ =
      some s₂) :
    s₂.store.shape = s₀.store.shape ∧ s₂.pos = s₀.pos ∧
      pairLayout.Holds s₂.store p H.Ua (2 * (n * n) * D + 2 * n * lo)
        ((eighTapeMachine I p mmR qrR).identityMat k) ∧
      (∀ i : Fin k, s₂.store.read p H.Ea (n * D + lo + i) =
        some (eighTapeMachine I p mmR qrR).zero) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * D + 2 * n * lo ∨
        2 * (n * n) * D + 2 * n * lo + 2 * (k * k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * D + lo ∨ n * D + lo + k ≤ i) →
        s₂.store.read q b i = s₀.store.read q b i := by
  rw [exec_run_bind I (b := zidentity (ι := ι) p (.var k) H.Ua
    (eighBlockOff (.const n) (.const D) (.var lo))) (fun _ => rfl)] at h
  obtain ⟨s₄, hz, h⟩ := Option.bind_eq_some_iff.mp h
  have hU := (holds_of_exec_zidentity (mmR := mmR) (qrR := qrR)
    (toNat := fun x => (I.sem.toNat p x).getD 0) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) p k
    ((exec_zidentity_congr I p _ _ _ _).symm.trans hz)).1
  change exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) .skip))) .skip) _ = _ at hz
  rw [exec_seq_skip, exec_named, exec_seq] at hz
  obtain ⟨σ, h₀, h₁⟩ := Option.bind_eq_some_iff.mp hz
  rw [exec_seq_skip] at h₁
  change exec I (.seq (.loop _ _) .skip) _ = _ at h
  rw [exec_seq_skip] at h
  obtain ⟨hsh₀, hps₀, -, hfr₀⟩ := read_of_exec_loop_lit h₀
  obtain ⟨hsh₁, hps₁, -, hfr₁⟩ := read_of_exec_loop_lit h₁
  obtain ⟨hsh₂, hps₂, hE, hfr₂⟩ := read_of_exec_loop_lit h
  simp only [eighBlockOff, eighSlotOff, zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat,
    IExp.eval_const, IExp.eval_var] at hU hfr₀ hfr₁ hfr₂ hE
  have hF : ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * D + 2 * n * lo ∨
      2 * (n * n) * D + 2 * n * lo + 2 * (k * k) ≤ i) →
      (b ≠ H.Ea ∨ i < n * D + lo ∨ n * D + lo + k ≤ i) →
      s₂.store.read q b i = s₀.store.read q b i := by
    intro q b i hU' hE'
    rw [hfr₂ q b i (hE'.imp_right fun h w hw => by omega),
      hfr₁ q b i (hU'.imp_right fun h w hw => by
        have : w + k * w < k * k := by nlinarith
        omega),
      hfr₀ q b i (hU'.imp_right fun h w hw => by omega)]
  refine ⟨hsh₂.trans (hsh₁.trans hsh₀), hps₂.trans (hps₁.trans hps₀),
    hU.of_forall_read_eq fun i _ _ => hfr₂ p _ i (Or.inl hUE), fun i => ?_, hF⟩
  obtain ⟨z, hz, hr⟩ := hE i i.isLt
  rw [hr]
  simp only [eighTapeMachine, ScalarSem.toFloatMachine, hz, Option.getD_some]

/-- One slot of the spent level: the node at the slot (if any) gets the stored identity and zero
eigenvalues; the shape, the tape positions, every cell outside depth $D$ of the output and
eigenvalue arenas, and the outputs of the slots below are kept. -/
private theorem eighBottomLevel_step (p : P) (n ℓ₀ F D : ℕ) (H : EighArenas)
    {st s₁ s₂ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {lo : ℕ}
    (hlo : lo < n) (hH : H.Shaped st.store p n D)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ D)
    (hsh : s₁.store.shape = st.store.shape) (hps : s₁.pos = st.pos)
    (hfr : ∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i) →
      s₁.store.read q b i = st.store.read q b i)
    (hdone : ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = D →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
      lo' < lo →
      pairLayout.Holds s₁.store p H.Ua (2 * (n * n) * D + 2 * n * lo')
          ((eighTapeMachine I p mmR qrR).identityMat y.k) ∧
        ∀ i : Fin y.k, s₁.store.read p H.Ea (n * D + lo' + i) =
          some (eighTapeMachine I p mmR qrR).zero)
    (h : exec I (Builder.bindIdx (ι := ι) p ⟨H.Sz, eighSlotOff (.const n) (.const D) (.var lo)⟩
      (.const n - .var lo) fun k => eighWhen (.var k) do
        zidentity p (.var k) H.Ua (eighBlockOff (.const n) (.const D) (.var lo))
        forRange (.var k) fun i =>
          ins (.lit p ⟨H.Ea, eighSlotOff (.const n) (.const D) (.var lo) + .var i⟩ 0)).run s₁ =
      some s₂) :
    s₂.store.shape = st.store.shape ∧ s₂.pos = st.pos ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i) →
        s₂.store.read q b i = st.store.read q b i) ∧
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = D →
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
        lo' < lo + 1 →
        pairLayout.Holds s₂.store p H.Ua (2 * (n * n) * D + 2 * n * lo')
            ((eighTapeMachine I p mmR qrR).identityMat y.k) ∧
          ∀ i : Fin y.k, s₂.store.read p H.Ea (n * D + lo' + i) =
            some (eighTapeMachine I p mmR qrR).zero := by
  obtain ⟨hnd, -, -, -, -, -, -⟩ := hH
  simp only [EighArenas.handles, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s₁ = some s₂ at h
  rw [exec_seq_skip] at h
  have hSzfr : ∀ q i, s₁.store.read q H.Sz i = st.store.read q H.Sz i := fun q i =>
    hfr q _ i (fun h => h.1.elim (fun e => hnd.2.1.2.2.1 e.symm) (fun e => hnd.2.2.2.1.1 e.symm))
  by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = D ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
  swap
  · push Not at hy
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.2.1 lo hlo fun a y ha => hy a y ha)
    rw [exec_bindIdx_of_read I ((hSzfr p _).trans hv) hk (Nat.zero_le _)] at h
    change exec I (.seq (.loop _ _) .skip) _ = some s₂ at h
    rw [exec_seq_skip, exec_loop] at h
    simp only [IExp.eval_sub, IExp.eval_one, IExp.eval_var, Nat.sub_zero,
      Nat.sub_self, List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    refine ⟨hsh, hps, hfr, fun a lo' y ha hay hlt =>
      hdone a lo' y ha hay (lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) ?_)⟩
    rintro rfl
    exact hy a y ha hay
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hay).1
  have hb := eighLoc_bounds (by omega : 1 ≤ n) hay
  rw [exec_bindIdx_of_read I ((hSzfr p _).trans hv) hk
    (by simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var]; omega)] at h
  change exec I (.seq (.loop _ _) .skip) _ = some s₂ at h
  rw [exec_seq_skip, exec_loop] at h
  rw [show (1 - (1 - IExp.var y.k) : IExp ℕ).eval = 1 by
    simp only [IExp.eval_sub, IExp.eval_one, IExp.eval_var]; omega, List.range_one,
    List.foldlM_cons] at h
  simp only [List.foldlM_nil, bind_pure] at h
  have hUE : H.Ua ≠ H.Ea := hnd.2.1.2.1
  obtain ⟨hsh₂, hps₂, hU, hE, hF⟩ := eighBottomLevel_node_run p n D lo y.k H hUE h
  have hkn : y.k ≤ n := by omega
  have hblk : 2 * n * lo + 2 * (y.k * y.k) ≤ 2 * (n * n) := by
    nlinarith [Nat.mul_le_mul_left n hb.2, Nat.mul_le_mul_right y.k hkn]
  refine ⟨hsh₂.trans hsh, hps₂.trans hps,
    fun q b i hb' => (hF q b i ?_ ?_).trans (hfr q b i hb'), ?_⟩
  · by_contra hc
    push Not at hc
    refine hb' ⟨Or.inl hc.1, Or.inl ⟨Or.inr (Or.inl hc.1), by omega, ?_⟩⟩
    rw [Nat.mul_succ]
    omega
  · by_contra hc
    push Not at hc
    refine hb' ⟨Or.inr hc.1, Or.inr (Or.inl ⟨Or.inl hc.1, by omega, ?_⟩)⟩
    rw [Nat.mul_succ]
    omega
  intro a' lo' y' ha' hay' hlt
  have hb' := eighLoc_bounds (by omega : 1 ≤ n) hay'
  by_cases haa : a' = a
  · subst haa
    rw [hay] at hay'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hay')
    exact ⟨hU, hE⟩
  have hdis := eighLoc_disjoint (ha'.trans ha.symm) haa hay' hay
  have hlt' : lo' + y'.k ≤ lo := by omega
  obtain ⟨hU', hE'⟩ := hdone a' lo' y' ha' hay' (by omega)
  refine ⟨hU'.of_forall_read_eq fun i _ hi => hF p _ i (Or.inr (Or.inl ?_)) (Or.inl hUE),
    fun i => (hF p _ _ (Or.inl hUE.symm) (Or.inr (Or.inl (by omega)))).trans (hE' i)⟩
  change i < _ + y'.k * y'.k * 2 at hi
  nlinarith [Nat.mul_le_mul_left n hlt', Nat.mul_le_mul_right y'.k (by omega : y'.k ≤ n)]

/-- **The spent level writes the junk outputs**: under exact integer literals up to $n + 4$ and the
exact floor conversion, a successful run of `NLAlib.eighBottomLevel` at depth $D$ from a state whose
arenas hold the nodes of depth $D$ ends with the outputs of depth $D$ holding `NLAlib.eighAux` at
budget $0$ (`NLAlib.EighArenas.OutHolds` at $D$: the machine's identity and zeros); every cell
outside the output and eigenvalue arenas at depth $D$ is unchanged, the store shape and the tape
positions too. No printed source.
Proof: the loop over the slots as in `NLAlib.holds_of_exec_eighDownLevel`, each node by the pilot's
`NLAlib.Computation.holds_of_exec_zidentity` (after `NLAlib.Computation.exec_zidentity_congr`) and a
loop of literals; `NLAlib.eighAux` at budget $0$ is the identity and zeros by definition
(`Nat.sub_self`). M, about 60 lines. -/
theorem holds_of_exec_eighBottomLevel {dec : P → K → ℝ} (p : P) (n ℓ₀ F D : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ D)
    (h : exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) H.Ua H.Ea H.Sz).run st =
      some st') :
    H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ D ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  change exec I (.seq (.loop (.const n) _) .skip) st = some st' at h
  rw [exec_seq_skip] at h
  obtain ⟨hsh, hps, hfr, hdone⟩ := forall_of_exec_loop_eq_some I (n := .const n)
    (fun lo s => s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i) →
        s.store.read q b i = st.store.read q b i) ∧
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = D →
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
        lo' < lo →
        pairLayout.Holds s.store p H.Ua (2 * (n * n) * D + 2 * n * lo')
            ((eighTapeMachine I p mmR qrR).identityMat y.k) ∧
          ∀ i : Fin y.k, s.store.read p H.Ea (n * D + lo' + i) =
            some (eighTapeMachine I p mmR qrR).zero)
    ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun lo hlo s₁ s₂ ⟨hsh, hps, hfr, hdone⟩ hex =>
      eighBottomLevel_step p n ℓ₀ F D H hlo hH hlev hsh hps hfr hdone hex) h
  refine ⟨fun a lo y ha hay => ?_, hfr, hsh, hps⟩
  rw [Nat.sub_self]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- the root of size 0 is a leaf, so it is the only node, and its blocks are empty
    have hy0 : y.k = 0 := by
      cases a with
      | nil => cases hay; rfl
      | cons b a => simp [eighLoc, eighStep] at hay
    have hk : ∀ i : Fin y.k, False := fun i => absurd i.isLt (by omega)
    exact ⟨fun i => (hk i).elim, fun i => (hk i).elim⟩
  have hb := eighLoc_bounds hn hay
  exact hdone a lo y ha hay (by simp only [IExp.eval_const]; omega)

omit [Inhabited K] in
/-- A loop of literals into cells of one buffer inside its shape succeeds and keeps the shape and
every other buffer. -/
private theorem exists_exec_loop_lit_of_lt {p : P} {m : IExp ℕ} {Y len : ℕ} {f : ℕ → IExp ℕ}
    {c : ℚ} {st : St P K C} (hc : ∃ z, I.sem.lit p c = some z)
    (hY : st.store.shape[Y]? = some (p, len)) (hf : ∀ w < m.eval, (f w).eval < len) :
    ∃ st', exec I (.loop m fun w => .seq (.instr (.lit p ⟨Y, f w⟩ c)) .skip) st = some st' ∧
      st'.store.shape = st.store.shape ∧
      ∀ q b i, b ≠ Y → st'.store.read q b i = st.store.read q b i := by
  obtain ⟨z, hz⟩ := hc
  refine exists_exec_loop_eq_some_of_forall (I := I) (fun _ s => s.store.shape = st.store.shape ∧
      ∀ q b i, b ≠ Y → s.store.read q b i = st.store.read q b i) ⟨rfl, fun _ _ _ _ => rfl⟩ ?_
  rintro w hw s ⟨hsh, hrd⟩
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := s.store) z
    (hsh ▸ hY) (hf w hw)
  refine ⟨_, (exec_seq_instr_lit I hz hs').trans (exec_skip I _), ?_, fun q b i hb => ?_⟩
  · exact (Store.shape_of_write_eq_some hs').trans hsh
  · exact (Store.read_of_write_eq_some_of_ne hs' (Or.inl hb)).trans (hrd q b i hb)

/-- **The spent level succeeds** under the standard model with every value in range and the exact
floor conversion, when the arenas are allocated and their size cells of depth $D$ are initialised.
No printed source.
Proof: `NLAlib.Computation.exists_exec_loop_eq_some_of_forall`; each binder succeeds (`htn`), each
literal (`lit_ok`) and each write (the blocks fit, `NLAlib.eighLoc_bounds`, `hH`). S, about 30
lines. -/
theorem exists_exec_eighBottomLevel {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (htn : IsExactToNat dec I.sem) (p : P)
    (n ℓ₀ F D : ℕ) (H : EighArenas) {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hH : H.Shaped st.store p n D)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ D) :
    ∃ st', exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) H.Ua H.Ea H.Sz).run st =
      some st' := by
  obtain ⟨hnd, -, hUa, -, hEa, hSz, -⟩ := hH
  simp only [EighArenas.handles, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  change ∃ st', exec I (.seq (.loop (.const n) _) .skip) st = some st'
  simp only [exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall (I := I)
    (fun _ s => s.store.shape = st.store.shape ∧
      ∀ q i, s.store.read q H.Sz i = st.store.read q H.Sz i) ⟨rfl, fun _ _ => rfl⟩ ?_).imp
    fun _ h => h.1
  rintro lo hlo s ⟨hsh, hrd⟩
  simp only [IExp.eval_const] at hlo
  -- the size cell of the slot reads an index
  obtain ⟨v, hv, k, hk, hkn⟩ : ∃ v, st.store.read p H.Sz (n * D + lo) = some v ∧
      ∃ k, I.sem.toNat p v = some k ∧ k ≤ n - lo := by
    have : ∃ k, ReadsIdx I.sem st.store p H.Sz (n * D + lo) k ∧ k ≤ n - lo := by
      by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = D ∧
          eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
      · obtain ⟨a, y, ha, hy⟩ := hy
        obtain ⟨-, hb⟩ := eighLoc_bounds (by omega : 1 ≤ n) hy
        exact ⟨_, (hlev.1 a lo y ha hy).1, by omega⟩
      · push Not at hy
        exact ⟨0, hlev.2.1 lo hlo fun a y ha => hy a y ha, Nat.zero_le _⟩
    obtain ⟨k, hk, hkn⟩ := this
    unfold ReadsIdx at hk
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hk
    exact ⟨v, hv, k, hk, hkn⟩
  have hx : s.store.read p H.Sz (n * D + lo) = some v := (hrd p _).trans hv
  change ∃ st', exec I (.seq (.bindIdx p ⟨H.Sz, eighSlotOff (.const n) (.const D) (.var lo)⟩
    (.const n - .var lo) _) .skip) s = some st' ∧ _
  rw [exec_seq_skip, exec_bindIdx_of_read I hx hk (by exact hkn)]
  have hk' : k ≤ n - lo := hkn
  generalize k = k' at hk' ⊢
  change ∃ st', exec I (.seq (.loop _ fun _ => _) .skip) _ = some st' ∧ _
  rw [exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall (I := I)
    (fun _ s => s.store.shape = st.store.shape ∧
      ∀ q i, s.store.read q H.Sz i = st.store.read q H.Sz i) ⟨hsh, hrd⟩ ?_
  rintro - - s₁ ⟨hsh₁, hrd₁⟩
  have hlit : ∀ c : ℚ, ∃ z, I.sem.lit p c = some z := fun c => hsem.lit_ok p c trivial
  have hblk : 2 * n * lo + 2 * (k' * k') ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul hk' hk'
    have h2 : n - lo + lo = n := Nat.sub_add_cancel hlo.le
    nlinarith
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) .skip)))
    (.seq (.loop _ _) .skip)) s₁ = some st' ∧ _
  obtain ⟨s₂, h₂, hsh₂, hrd₂⟩ := exists_exec_loop_lit_of_lt (I := I)
    (m := 2 * (.var k' * .var k')) (Y := H.Ua)
    (f := fun w => eighBlockOff (.const n) (.const D) (.var lo) + .var w) (hlit 0)
    (hsh₁ ▸ hUa) (by
      intro w hw
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat, IExp.eval_const,
        IExp.eval_var] at hw ⊢
      nlinarith)
  obtain ⟨s₃, h₃, hsh₃, hrd₃⟩ := exists_exec_loop_lit_of_lt (I := I) (st := s₂)
    (m := .var k') (Y := H.Ua)
    (f := fun i => eighBlockOff (.const n) (.const D) (.var lo) + zidx (.var k') (.var i) (.var i))
    (hlit 1) ((hsh₂.trans hsh₁) ▸ hUa) (by
      intro i hi
      simp only [eighBlockOff, zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat,
        IExp.eval_const, IExp.eval_var] at hi ⊢
      nlinarith)
  obtain ⟨s₄, h₄, hsh₄, hrd₄⟩ := exists_exec_loop_lit_of_lt (I := I) (st := s₃)
    (m := .var k') (Y := H.Ea)
    (f := fun i => eighSlotOff (.const n) (.const D) (.var lo) + .var i)
    (hlit 0) ((hsh₃.trans (hsh₂.trans hsh₁)) ▸ hEa) (by
      intro i hi
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var] at hi ⊢
      rw [Nat.mul_succ]
      omega)
  refine ⟨s₄, ?_, hsh₄.trans (hsh₃.trans (hsh₂.trans hsh₁)), fun q i => ?_⟩
  · rw [exec_seq, exec_named, exec_seq]
    exact Option.bind_eq_some_iff.mpr ⟨s₃, Option.bind_eq_some_iff.mpr ⟨s₂, h₂, by
      rw [exec_seq_skip]; exact h₃⟩, by rw [exec_seq_skip]; exact h₄⟩
  · rw [hrd₄ q _ i (Ne.symm hnd.2.2.2.1.1), hrd₃ q _ i (Ne.symm hnd.2.1.2.2.1),
      hrd₂ q _ i (Ne.symm hnd.2.1.2.2.1)]
    exact hrd₁ q i

/-- A one-child step adds back the shift $\pm\mathrm{fl}(R/2)$. -/
private theorem el5_eighStep_shift {F Su Sg : Type*} [Inhabited Sg] {M : FloatMachine F Su Sg}
    {N fuel k ℓ : ℕ} {R₀ β R ε : F} {A : Matrix (Fin k) (Fin k) (F × F)} {s : EighSample Su Sg N}
    {b : Bool} {A' : Matrix (Fin k) (Fin k) (F × F)} {σ : F}
    (h : eighStep M N fuel R₀ β A R ε ℓ s = .shift b A' σ) :
    σ = if b then M.div R (M.ofNat 2) else M.neg (M.div R (M.ofNat 2)) := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h <;> cases h <;> rfl

/-- A split adds back the shift $\mathrm{fl}(R/2)$ and has $0 < k_+ < k$. -/
private theorem el5_eighStep_split {F Su Sg : Type*} [Inhabited Sg] {M : FloatMachine F Su Sg}
    {N fuel k ℓ : ℕ} {R₀ β R ε : F} {A : Matrix (Fin k) (Fin k) (F × F)} {s : EighSample Su Sg N}
    {kp : ℕ} {hkp : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (h : eighStep M N fuel R₀ β A R ε ℓ s = .split kp hkp Qp Qm Ap Am σ) :
    σ = M.div R (M.ofNat 2) ∧ 0 < kp ∧ kp < k := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4
  cases h
  exact ⟨rfl, Nat.pos_of_ne_zero h4, lt_of_le_of_ne (min_le_left _ _) h3⟩

/-- A successful loop of binary operations `Y[f w] ← Y[g w] ∘ c` whose written cells are distinct
and never read: the written cells hold the results, every other cell is kept. -/
private theorem el5_binLoop {p : P} {op : BinOp} {m : IExp ℕ} {Y : ℕ} {c : Cell ℕ ℕ}
    {f g : ℕ → IExp ℕ} {st st' : St P K C} (hYc : c.buf ≠ Y)
    (hfg : ∀ w < m.eval, ∀ w' < m.eval, (f w).eval ≠ (g w').eval)
    (hf : ∀ w < m.eval, ∀ w' < m.eval, (f w).eval = (f w').eval → w = w')
    (h : exec I (.loop m fun w => .seq (.instr (.bin p op ⟨Y, f w⟩ ⟨Y, g w⟩ c)) .skip) st =
      some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ w < m.eval, ∀ x z, st.store.read p Y (g w).eval = some x →
        st.store.read p c.buf c.idx.eval = some z →
        st'.store.read p Y (f w).eval = some ((I.sem.bin p op x z).getD default)) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w < m.eval, (f w).eval ≠ i) →
        st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧
      (∀ w' < w, ∀ x z, st.store.read p Y (g w').eval = some x →
        st.store.read p c.buf c.idx.eval = some z →
        s.store.read p Y (f w').eval = some ((I.sem.bin p op x z).getD default)) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w' < w, (f w').eval ≠ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w hw s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨a, ha, b, hb, v, hv, s', hw', rfl⟩, rfl⟩ := hex
  have hga : s₁.store.read p Y (g w).eval = st.store.read p Y (g w).eval :=
    hfr p Y _ (Or.inr fun w' hw' => hfg w' (by omega) w hw)
  have hcb : s₁.store.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval :=
    hfr p _ _ (Or.inl hYc)
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun w' hw'' x z hx hz => ?_,
    fun q b' i hb' => ?_⟩
  · by_cases hww : w' = w
    · subst hww
      rw [Store.read_of_write_eq_some hw']
      rw [hga, hx] at ha
      rw [hcb, hz] at hb
      cases ha; cases hb
      simp [hv]
    · have hlt : w' < w := lt_of_le_of_ne (Nat.lt_succ_iff.mp hw'') hww
      rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr fun e => hww (hf w' (by omega) w hw e))]
      exact hrd w' hlt x z hx hz
  · rw [Store.read_of_write_eq_some_of_ne hw' ?_]
    · exact hfr q b' i (hb'.imp_right fun h w' hw' => h w' (by omega))
    · exact hb'.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

omit [AddMonoid C] [Inhabited K] in
/-- Two column blocks stored one after the other hold the matrix of their columns. -/
private theorem el5_holds_fromCols {s : Store P K} {p : P} {b off k kp : ℕ} (h : kp ≤ k)
    {X : Matrix (Fin k) (Fin kp) (K × K)} {Y : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    (hX : pairLayout.Holds s p b off X) (hY : pairLayout.Holds s p b (off + 2 * (k * kp)) Y) :
    pairLayout.Holds s p b off ((Matrix.fromCols X Y).submatrix id
      ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm)) := by
  intro i j t
  by_cases hj : (j : ℕ) < kp
  · have e : ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j =
        Sum.inl ⟨j, hj⟩ := by
      simp only [Equiv.trans_apply]
      rw [Equiv.symm_apply_eq]
      ext; simp
    simp only [Matrix.submatrix_apply, id, e, Matrix.fromCols_apply_inl]
    exact hX i ⟨j, hj⟩ t
  · have e : ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j =
        Sum.inr ⟨j - kp, by omega⟩ := by
      simp only [Equiv.trans_apply]
      rw [Equiv.symm_apply_eq]
      ext; simp; omega
    simp only [Matrix.submatrix_apply, id, e, Matrix.fromCols_apply_inr]
    have := hY i ⟨j - kp, by omega⟩ t
    rw [← this]
    congr 1
    simp only [pairLayout]
    have : (j : ℕ) = kp + (j - kp) := by omega
    conv_lhs => rw [this]
    ring

omit [AddMonoid C] [Inhabited K] in
private theorem el5_bd {b i B off len : ℕ} (h : b ≠ B ∨ i < off ∨ off + len ≤ i) :
    blockDisjoint (b, i, 1) (B, off, len) = true := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  omega

omit [AddMonoid C] [Inhabited K] in
private theorem el5_bd2 {b b' off off' len len' : ℕ}
    (h : off + len ≤ off' ∨ off' + len' ≤ off) :
    blockDisjoint (b, off, len) (b', off', len') = true := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  omega

omit [AddMonoid C] [Inhabited K] in
private theorem el5_bd2' {b b' off off' len len' : ℕ} (h : b ≠ b' ∨ off + len ≤ off') :
    blockDisjoint (b, off, len) (b', off', len') = true := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- The branch of a one-child node in the upward pass: the child's output copied, the shift
added to its eigenvalues. -/
private theorem el5_shift_run (p : P) (n d lo k : ℕ) (H : EighArenas) (tc : Cell ℕ ℕ)
    {s s' : St P K C} (hk : lo + k ≤ n) (hUE : H.Ua ≠ H.Ea) (htc : tc.buf ≠ H.Ea)
    (htcU : tc.buf ≠ H.Ua)
    {U : Matrix (Fin k) (Fin k) (K × K)} {e : Fin k → K} {σ : K}
    (hU : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U)
    (hE : ∀ i : Fin k, s.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i))
    (hσ : s.store.read p tc.buf tc.idx.eval = some σ)
    (h : exec I (do
        zcopy (ι := ι) p (IExp.var k) (IExp.var k) H.Ua
          (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))
          H.Ua (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
        forRange (IExp.var k) fun i => ins (.bin p .add
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
          tc)).run s = some s') :
    s'.store.shape = s.store.shape ∧ s'.pos = s.pos ∧
      pairLayout.Holds s'.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
      (∀ i : Fin k, s'.store.read p H.Ea (n * d + lo + i) =
        some ((I.sem.bin p .add (e i) σ).getD default)) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) →
        s'.store.read q b i = s.store.read q b i := by
  rw [exec_run_bind I (b := zcopy (ι := ι) p (IExp.var k) (IExp.var k) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))) (fun _ => rfl)] at h
  obtain ⟨s₁, hz, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_zcopy_congr] at hz
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  obtain ⟨hU₁, hfr₁, hsh₁, hps₁⟩ := holds_of_exec_zcopy p k k
    (xo := eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))
    (yo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)) (A := U)
    (by simpa [eighBlockOff, Nat.mul_succ] using hU)
    (el5_bd2 (Or.inl (by
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var, IExp.eval_ofNat]
      rw [Nat.mul_succ]; omega))) hz
  simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
    IExp.eval_ofNat] at hU₁ hfr₁
  change exec I (.seq (.loop _ _) .skip) _ = _ at h
  rw [exec_seq_skip] at h
  obtain ⟨hsh₂, hps₂, hE₂, hfr₂⟩ := el5_binLoop htc (by
    intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw hw' ⊢
    rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h
  simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
    IExp.eval_ofNat] at hE₂ hfr₂
  have hfr : ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
      2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
      (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) →
      s'.store.read q b i = s.store.read q b i := by
    intro q b i hU' hE'
    rw [hfr₂ q b i (hE'.imp_right fun h w hw => by omega), hfr₁ q b i (el5_bd hU')]
  refine ⟨hsh₂.trans hsh₁, hps₂.trans hps₁,
    hU₁.of_forall_read_eq fun i _ _ => hfr₂ p _ i (Or.inl hUE), fun i => ?_, hfr⟩
  have hx : s₁.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i) := by
    rw [hfr₁ p _ _ (el5_bd (Or.inl (Ne.symm hUE)))]; exact hE i
  have hz : s₁.store.read p tc.buf tc.idx.eval = some σ := by
    rw [hfr₁ p _ _ (el5_bd (Or.inl htcU))]; exact hσ
  have := hE₂ i i.isLt (e i) σ (by rw [Nat.mul_succ] at hx ⊢; simpa [Nat.mul_succ] using hx) hz
  exact this

/-- The branch of a split in the upward pass: the two products into the column blocks of the
node's output, the shifted eigenvalues of the two children. -/
private theorem el5_split_run {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n d lo k kp t : ℕ) (H : EighArenas) {s s' : St P K C} (hk : lo + k ≤ n) (hkp : kp < k)
    (hUE : H.Ua ≠ H.Ea) (hUQ : H.Ua ≠ H.Qa) (htE : t ≠ H.Ea) (htU : t ≠ H.Ua)
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Up : Matrix (Fin kp) (Fin kp) (K × K)} {Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    {ep : Fin kp → K} {em : Fin (k - kp) → K} {σ : K}
    (hQp : pairLayout.Holds s.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds s.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (hUp : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up)
    (hUm : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um)
    (hEp : ∀ j : Fin kp, s.store.read p H.Ea (n * (d + 1) + lo + j) = some (ep j))
    (hEm : ∀ j : Fin (k - kp), s.store.read p H.Ea (n * (d + 1) + (lo + kp) + j) = some (em j))
    (hσ : s.store.read p t 0 = some σ)
    (h : exec I (do
        let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
        stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
          [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
          [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
        stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp, IExp.var k - IExp.var kp]
          [(H.Qa, qo + 2 * (IExp.var k * IExp.var kp)),
            (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo + IExp.var kp))]
          [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
            2 * (IExp.var k * IExp.var kp))])
        forRange (IExp.var kp) fun j => ins (.bin p .add
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩ ⟨t, 0⟩)
        forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp + IExp.var j⟩
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
            IExp.var j⟩ ⟨t, 0⟩)).run s = some s') :
    s'.store.shape = s.store.shape ∧ s'.pos = s.pos ∧
      pairLayout.Holds s'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
        ((Matrix.fromCols (mmR Qp Up) (mmR Qm Um)).submatrix id
          ((finCongr (Nat.add_sub_of_le hkp.le).symm).trans finSumFinEquiv.symm)) ∧
      (∀ j : Fin kp, s'.store.read p H.Ea (n * d + lo + j) =
        some ((I.sem.bin p .add (ep j) σ).getD default)) ∧
      (∀ j : Fin (k - kp), s'.store.read p H.Ea (n * d + lo + kp + j) =
        some ((I.sem.bin p .sub (em j) σ).getD default)) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) →
        s'.store.read q b i = s.store.read q b i := by
  change exec I (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.loop _ _) (.seq (.loop _ _) .skip)))) s = some s' at h
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
  rw [exec_seq] at h
  obtain ⟨s₃, h₃, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq_skip] at h
  simp only [List.map_cons, List.map_nil, eighBlockOff, IExp.eval_add, IExp.eval_mul,
    IExp.eval_const, IExp.eval_var, IExp.eval_ofNat, IExp.eval_sub] at hu₁ hu₂
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  have hkpk : k * kp ≤ k * k := Nat.mul_le_mul_left k hkp.le
  have hsplit : k * kp + k * (k - kp) = k * k := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hkp.le]
  have hlok : lo * n + k * n ≤ n * n := by nlinarith
  obtain ⟨hP, hfr₁⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p (l := k) (m := kp)
    (n := kp) (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * lo))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo)) hQp hUp
    (el5_bd2' (Or.inl hUQ))
    (el5_bd2 (Or.inl (by simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith)))
    hu₁
  have hQm₁ := hQm.of_forall_read_eq fun i _ _ => hfr₁ p _ i (el5_bd (Or.inl (Ne.symm hUQ)))
  have hUm₁ := hUm.of_forall_read_eq fun i hi _ => hfr₁ p _ i (el5_bd (Or.inr (Or.inr (by
    simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith))))
  obtain ⟨hM, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p (l := k)
    (m := k - kp) (n := k - kp) (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * (lo + kp)))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))) hQm₁ hUm₁
    (el5_bd2' (Or.inl hUQ)) (el5_bd2 (Or.inl (by
      simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith))) (by convert hu₂ using 3)
  have hP₂ := hP.of_forall_read_eq fun i _ hi => hfr₂ p _ i (el5_bd (Or.inr (Or.inl (by
    simp only [pairLayout] at hi; nlinarith))))
  -- the eigenvalue loops
  obtain ⟨hsh₃, hps₃, hE₃, hfr₃⟩ := el5_binLoop (c := ⟨t, 0⟩) htE (by
    intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw hw' ⊢
    rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h₃
  obtain ⟨hsh₄, hps₄, hE₄, hfr₄⟩ := el5_binLoop (c := ⟨t, 0⟩) htE (by
    intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat, IExp.eval_sub] at hw hw' ⊢
    rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h
  simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
    IExp.eval_ofNat, IExp.eval_sub] at hE₃ hfr₃ hE₄ hfr₄
  have hsh₁ := Interp.shape_of_kcallStore_eq_some hu₁
  have hsh₂ := Interp.shape_of_kcallStore_eq_some hu₂
  have hc1 : (k - kp) * k = k * (k - kp) := Nat.mul_comm _ _
  have hc2 : kp * k = k * kp := Nat.mul_comm _ _
  have hfr : ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
      2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
      (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) →
      s'.store.read q b i = s.store.read q b i := by
    intro q b i hU' hE'
    rw [hfr₄ q b i (hE'.imp_right fun h w hw => by omega),
      hfr₃ q b i (hE'.imp_right fun h w hw => by omega),
      hfr₂ q b i (el5_bd (hU'.imp_right fun h => by simp only [pairLayout]; omega)),
      hfr₁ q b i (el5_bd (hU'.imp_right fun h => by simp only [pairLayout]; omega))]
  have hrdE : ∀ i, u₂.read p H.Ea i = s.store.read p H.Ea i := fun i => by
    rw [hfr₂ p _ i (el5_bd (Or.inl (Ne.symm hUE))), hfr₁ p _ i (el5_bd (Or.inl (Ne.symm hUE)))]
  have hrdt : u₂.read p t 0 = some σ := by
    rw [hfr₂ p _ _ (el5_bd (Or.inl htU)), hfr₁ p _ _ (el5_bd (Or.inl htU))]; exact hσ
  refine ⟨hsh₄.trans (hsh₃.trans (hsh₂.trans hsh₁)), hps₄.trans hps₃, ?_, fun j => ?_,
    fun j => ?_, hfr⟩
  · refine (el5_holds_fromCols hkp.le hP₂ hM).of_forall_read_eq fun i _ _ => ?_
    rw [hfr₄ p _ i (Or.inl hUE), hfr₃ p _ i (Or.inl hUE)]
  · rw [hfr₄ p _ _ (Or.inr fun w hw => by omega)]
    exact hE₃ j j.isLt (ep j) σ (by rw [hrdE, Nat.mul_succ]; simpa [Nat.mul_succ] using hEp j) hrdt
  · have := hE₄ j j.isLt (em j) σ (by
      rw [hfr₃ p _ _ (Or.inr fun w hw => by rw [Nat.mul_succ]; omega), hrdE,
        show n * (d + 1) + lo + kp + j = n * (d + 1) + (lo + kp) + j by omega]
      exact hEm j) (by rw [hfr₃ p _ _ (Or.inl htE)]; exact hrdt)
    exact this


omit [Inhabited K] in
private theorem el5_seq_loop_zero {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} (he : e.eval = 0) : exec I (.seq (.loop e b) t) s = exec I t s := by
  rw [exec_seq, exec_loop, he]
  simp

omit [Inhabited K] in
private theorem el5_seq_loop_one {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} (he : e.eval = 1) :
    exec I (.seq (.loop e b) t) s = (exec I (b 0) s).bind (exec I t) := by
  rw [exec_seq, exec_loop, he]
  simp [List.range_one]

omit [Inhabited K] in
/-- The column map of an assembled split: a column below $k_+$ is on the positive side. -/
private theorem el5_e_inl {k kp : ℕ} (h : kp ≤ k) (j : Fin k) (hj : (j : ℕ) < kp) :
    ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j = Sum.inl ⟨j, hj⟩ := by
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq]
  ext; simp

omit [Inhabited K] in
/-- The column map of an assembled split: a column from $k_+$ is on the negative side. -/
private theorem el5_e_inr {k kp : ℕ} (h : kp ≤ k) (j : Fin k) (hj : kp ≤ (j : ℕ)) :
    ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j =
      Sum.inr ⟨j - kp, by omega⟩ := by
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq]
  ext; simp; omega

omit [AddMonoid C] [Inhabited K] in
/-- The distinct handles of the arenas that the upward pass touches. -/
private theorem el5_hne {H : EighArenas} (hnd : H.handles.Nodup) :
    H.Ua ≠ H.Ea ∧ H.Ua ≠ H.Qa ∧ H.Kd ≠ H.Ua ∧ H.Kd ≠ H.Ea ∧ H.Kp ≠ H.Ua ∧ H.Kp ≠ H.Ea ∧
      H.Qa ≠ H.Ea ∧ H.Sz ≠ H.Ua ∧ H.Sz ≠ H.Ea ∧ H.Ma ≠ H.Ua ∧ H.Ma ≠ H.Ea ∧ H.Lv ≠ H.Ua ∧
      H.Lv ≠ H.Ea := by
  simp only [EighArenas.handles, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> simp_all

omit [AddMonoid C] [Inhabited K] in
private theorem el5_lc_Ua {H : EighArenas} {n d i : ℕ} (hnd : H.handles.Nodup)
    (h : H.LevelCell n d H.Ua i) : 2 * (n * n) * d ≤ i ∧ i < 2 * (n * n) * (d + 1) := by
  obtain ⟨h1, -, h3, -, h5, -, -, h8, -, -, -, h12, -⟩ := el5_hne hnd
  rcases h with ⟨-, h⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
  · exact h
  · rcases hb with hb | hb | hb | hb
    exacts [absurd hb h1, absurd hb.symm h8, absurd hb.symm h3, absurd hb.symm h5]
  · exact absurd hb.symm h12

omit [AddMonoid C] [Inhabited K] in
private theorem el5_lc_Ea {H : EighArenas} {n d i : ℕ} (hnd : H.handles.Nodup)
    (h : H.LevelCell n d H.Ea i) : n * d ≤ i ∧ i < n * (d + 1) := by
  obtain ⟨h1, -, -, -, -, -, h7, -, -, -, h11, -, h13⟩ := el5_hne hnd
  rcases h with ⟨hb, -⟩ | ⟨-, h⟩ | ⟨hb, -⟩
  · rcases hb with hb | hb | hb
    exacts [absurd hb.symm h11, absurd hb.symm h1, absurd hb.symm h7]
  · exact h
  · exact absurd hb.symm h13

/-- **One node of the upward pass**: the run of the kind binder at the node $y$ of slot $lo$
writes its output (`NLAlib.eighAux` at budget $D - d$) and keeps every cell outside the node's
output block and eigenvalue cells, when the cells it reads (outside depth $d$ of the output and
eigenvalue arenas, or inside the node's own) read as in `s₀`. -/
private theorem el5_node {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n ℓ₀ F d D : ℕ) (hn : 1 ≤ n) (hd : d < D) (H : EighArenas) (t : ℕ) {s₀ s₁ s₂ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {a : List Bool} {lo : ℕ}
    {y : EighNode K} (ha : a.length = d)
    (hay : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
      some (lo, y))
    (hnd : H.handles.Nodup) (htH : t ∉ H.handles)
    (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (ht1 : s₀.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
      ((eighTapeMachine I p mmR qrR).div (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
        ((eighTapeMachine I p mmR qrR).ofNat 2))))
    (hrec : H.RecordHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (hR : ∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ((b = H.Ua → 2 * (n * n) * d + 2 * n * lo ≤ i ∧
            i < 2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k)) ∧
          (b = H.Ea → n * d + lo ≤ i ∧ i < n * d + lo + y.k))) →
        s₁.store.read q b i = s₀.store.read q b i)
    (h : exec I (Builder.bindIdx (ι := ι) p
      ⟨H.Kd, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩ 4 fun c => do
        eighWhen (eighEqInd (IExp.var c) 2) do
          zcopy p (IExp.var y.k) (IExp.var y.k) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
          forRange (IExp.var y.k) fun i => ins (.bin p .add
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
            ⟨t, 0⟩)
        eighWhen (eighEqInd (IExp.var c) 3) do
          zcopy p (IExp.var y.k) (IExp.var y.k) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
          forRange (IExp.var y.k) fun i => ins (.bin p .add
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
            ⟨t, 1⟩)
        eighWhen (eighEqInd (IExp.var c) 4) <|
          Builder.bindIdx p ⟨H.Kp, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
            (IExp.var y.k) fun kp => do
            let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
            stmt (.kcall mm p [IExp.var y.k, IExp.var kp, IExp.var kp]
              [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
              [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
            stmt (.kcall mm p [IExp.var y.k, IExp.var y.k - IExp.var kp,
                IExp.var y.k - IExp.var kp]
              [(H.Qa, qo + 2 * (IExp.var y.k * IExp.var kp)),
                (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1)
                  (IExp.var lo + IExp.var kp))]
              [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
                2 * (IExp.var y.k * IExp.var kp))])
            forRange (IExp.var kp) fun j => ins (.bin p .add
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩
              ⟨t, 0⟩)
            forRange (IExp.var y.k - IExp.var kp) fun j => ins (.bin p .sub
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp +
                IExp.var j⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
                IExp.var j⟩ ⟨t, 0⟩)).run s₁ = some s₂) :
    s₂.store.shape = s₁.store.shape ∧ s₂.pos = s₁.pos ∧
      (pairLayout.Holds s₂.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).1 ∧
        ∀ i : Fin y.k, s₂.store.read p H.Ea (n * d + lo + i) = some
          ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).2 i)) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + y.k ≤ i) →
        s₂.store.read q b i = s₁.store.read q b i := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn hay
  obtain ⟨hyR, -, -⟩ := eighLoc_params hay
  rw [ha] at hyR
  obtain ⟨hUE, hUQ, hKdU, hKdE, hKpU, hKpE, hQE, -⟩ := el5_hne hnd
  have htU : t ≠ H.Ua := fun e => htH (e ▸ by simp [EighArenas.handles])
  have htE : t ≠ H.Ea := fun e => htH (e ▸ by simp [EighArenas.handles])
  have hRo : ∀ q b i, b ≠ H.Ua → b ≠ H.Ea → s₁.store.read q b i = s₀.store.read q b i :=
    fun q b i h1 h2 => hR q b i (Or.inl fun h => h.1.elim h1 h2)
  have hRU1 : ∀ q i, 2 * (n * n) * (d + 1) ≤ i → s₁.store.read q H.Ua i = s₀.store.read q H.Ua i :=
    fun q i hi => hR q _ i (Or.inl fun ⟨_, hc⟩ => by have := el5_lc_Ua hnd hc; omega)
  have hRE1 : ∀ q i, n * (d + 1) ≤ i → s₁.store.read q H.Ea i = s₀.store.read q H.Ea i :=
    fun q i hi => hR q _ i (Or.inl fun ⟨_, hc⟩ => by have := el5_lc_Ea hnd hc; omega)
  have hRW : ∀ q b i, (b = H.Ua → 2 * (n * n) * d + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k)) →
      (b = H.Ea → n * d + lo ≤ i ∧ i < n * d + lo + y.k) →
      s₁.store.read q b i = s₀.store.read q b i := fun q b i h1 h2 => hR q b i (Or.inr ⟨h1, h2⟩)
  have hr := hrec a lo y ha hay hk1
  rw [show D - d = (D - (d + 1)) + 1 by omega]
  -- the kind binder
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s₁ = some s₂ at h
  rw [exec_seq_skip] at h
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    rw [hs] at hr
    obtain ⟨hkd, hU, hE⟩ := hr
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hkd
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk (by decide)] at h
    change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _ at h
    rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, exec_skip] at h
    cases h
    refine ⟨rfl, rfl, ?_, fun _ _ _ _ _ => rfl⟩
    simp only [eighAux, eighSlotTree, hs]
    refine ⟨hU.of_forall_read_eq fun i hi hi' => hRW p _ i (fun _ => ⟨hi, ?_⟩)
      (fun h => absurd h hUE), fun i => (hRW p _ _ (fun h => absurd h.symm hUE)
      (fun _ => ⟨by omega, by omega⟩)).trans (hE i)⟩
    simpa [pairLayout, Nat.mul_comm] using hi'
  | shift b A' σ' =>
    rw [hs] at hr
    have hσ' := el5_eighStep_shift hs
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hr
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk (by split <;> decide)] at h
    have hch : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [b]) = some (lo,
        ⟨y.k, A', (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
          y.ℓ + 1⟩) := by
      rw [eighLoc_append_singleton, hay]
      simp [eighLoc, ha, hs]
    obtain ⟨hUc, hEc⟩ := hout (a ++ [b]) lo _ (by simp [ha]) hch
    have hUc' := hUc.of_forall_read_eq (s' := s₁.store) fun i hi _ => hRU1 p i (by omega)
    have hEc' : ∀ i : Fin y.k, s₁.store.read p H.Ea (n * (d + 1) + lo + i) = _ := fun i =>
      (hRE1 p _ (by omega)).trans (hEc i)
    change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _ at h
    cases b
    · rw [el5_seq_loop_zero rfl, el5_seq_loop_one rfl] at h
      obtain ⟨s₃, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      rw [el5_seq_loop_zero rfl, exec_skip] at h
      cases h
      obtain ⟨S1, S2, S3, S4, S5⟩ := el5_shift_run p n d lo y.k H ⟨t, 1⟩ hkn hUE htE htU
        (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) (h := h₁) hUc' hEc'
        ((hRo p _ _ htU htE).trans ht1)
      refine ⟨S1, S2, ?_, S5⟩
      simp only [eighAux, eighSlotTree, hs]
      refine ⟨S3, fun i => (S4 i).trans ?_⟩
      rw [hσ', hyR]
      rfl
    · rw [el5_seq_loop_one rfl] at h
      obtain ⟨s₃, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, exec_skip] at h
      cases h
      obtain ⟨S1, S2, S3, S4, S5⟩ := el5_shift_run p n d lo y.k H ⟨t, 0⟩ hkn hUE htE htU
        (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) (h := h₁) hUc' hEc'
        ((hRo p _ _ htU htE).trans ht0)
      refine ⟨S1, S2, ?_, S5⟩
      simp only [eighAux, eighSlotTree, hs]
      refine ⟨S3, fun i => (S4 i).trans ?_⟩
      rw [hσ', hyR]
      rfl
  | split kp hkp Qp Qm Ap Am σ' =>
    rw [hs] at hr
    obtain ⟨hσ', hkp0, hkpk⟩ := el5_eighStep_split hs
    obtain ⟨hkd, hkpr, hQp, hQm⟩ := hr
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hkd
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk (by decide)] at h
    change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _ at h
    rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, el5_seq_loop_one rfl] at h
    obtain ⟨s₃, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    rw [exec_skip] at h
    cases h
    obtain ⟨v', hv', hk'⟩ := Option.bind_eq_some_iff.mp hkpr
    change exec I (.seq (.bindIdx _ _ _ _) .skip) _ = some _ at h₁
    rw [exec_seq_skip, exec_bindIdx_of_read I ((hRo p _ _ hKpU hKpE).trans hv') hk'
      (by exact hkp)] at h₁
    have hchp : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [true]) = some (lo,
        ⟨kp, Ap, (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
          y.ℓ + 1⟩) := by
      rw [eighLoc_append_singleton, hay]
      simp [eighLoc, ha, hs]
    have hchm : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [false]) = some (lo + kp,
        ⟨y.k - kp, Am, (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
          y.ℓ + 1⟩) := by
      rw [eighLoc_append_singleton, hay]
      simp [eighLoc, ha, hs]
    obtain ⟨hUp, hEp⟩ := hout (a ++ [true]) lo _ (by simp [ha]) hchp
    obtain ⟨hUm, hEm⟩ := hout (a ++ [false]) (lo + kp) _ (by simp [ha]) hchm
    obtain ⟨S1, S2, S3, S4, S5, S6⟩ := el5_split_run hmm p n d lo y.k kp t H hkn hkpk hUE hUQ
      htE htU
      (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) + I.charge (.toNat p) }) (h := h₁)
      (hQp.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
      (hQm.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
      (hUp.of_forall_read_eq fun i hi _ => hRU1 p i (by omega))
      (hUm.of_forall_read_eq fun i hi _ => hRU1 p i (by nlinarith))
      (fun j => (hRE1 p _ (by omega)).trans (hEp j))
      (fun j => (hRE1 p _ (by omega)).trans (hEm j))
      ((hRo p _ _ htU htE).trans ht0)
    refine ⟨S1, S2, ?_, S6⟩
    simp only [eighAux, eighSlotTree, hs, ite_true, Bool.false_eq_true, ite_false]
    rw [← hyR] at S4 S5
    refine ⟨S3, fun i => ?_⟩
    by_cases hi : (i : ℕ) < kp
    · rw [el5_e_inl hkp i hi, Sum.elim_inl, hσ']
      exact S4 ⟨i, hi⟩
    · rw [el5_e_inr hkp i (by omega), Sum.elim_inr, hσ']
      have := S5 ⟨i - kp, by omega⟩
      rw [show n * d + lo + kp + (i - kp) = n * d + lo + i by omega] at this
      exact this

/-- **One slot of the upward pass**: the node at the slot (if any) gets its output; the shape,
the tape positions, every cell outside the blocks of the nodes at the slots up to $lo$, and the
outputs of the slots below are kept. -/
private theorem el5_step {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (H : EighArenas) (t : ℕ) {s₀ s₁ s₂ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {lo : ℕ} (hlo : lo < n)
    (hnd : H.handles.Nodup) (htH : t ∉ H.handles)
    (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (ht1 : s₀.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
      ((eighTapeMachine I p mmR qrR).div (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
        ((eighTapeMachine I p mmR qrR).ofNat 2))))
    (hlev : H.LevelHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (hsh : s₁.store.shape = s₀.store.shape) (hps : s₁.pos = s₀.pos)
    (hfr : ∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
          eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
            some (lo', y) → lo' < lo →
          (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
            2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
          (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
        s₁.store.read q b i = s₀.store.read q b i)
    (hdone : ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
      lo' < lo →
      pairLayout.Holds s₁.store p H.Ua (2 * (n * n) * d + 2 * n * lo')
          (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo' y)).1 ∧
        ∀ i : Fin y.k, s₁.store.read p H.Ea (n * d + lo' + i) = some
          ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo' y)).2 i))
    (h : exec I (Builder.bindIdx (ι := ι) p
      ⟨H.Sz, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
      (IExp.const n - IExp.var lo) fun k => eighWhen (IExp.var k) <| Builder.bindIdx p
        ⟨H.Kd, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩ 4 fun c => do
          eighWhen (eighEqInd (IExp.var c) 2) do
            zcopy p (IExp.var k) (IExp.var k) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
            forRange (IExp.var k) fun i => ins (.bin p .add
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
              ⟨t, 0⟩)
          eighWhen (eighEqInd (IExp.var c) 3) do
            zcopy p (IExp.var k) (IExp.var k) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
            forRange (IExp.var k) fun i => ins (.bin p .add
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
              ⟨t, 1⟩)
          eighWhen (eighEqInd (IExp.var c) 4) <|
            Builder.bindIdx p ⟨H.Kp, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
              (IExp.var k) fun kp => do
              let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
              stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
                [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
                [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
              stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp,
                  IExp.var k - IExp.var kp]
                [(H.Qa, qo + 2 * (IExp.var k * IExp.var kp)),
                  (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1)
                    (IExp.var lo + IExp.var kp))]
                [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
                  2 * (IExp.var k * IExp.var kp))])
              forRange (IExp.var kp) fun j => ins (.bin p .add
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩
                ⟨t, 0⟩)
              forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp +
                  IExp.var j⟩
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
                  IExp.var j⟩ ⟨t, 0⟩)).run s₁ = some s₂) :
    s₂.store.shape = s₀.store.shape ∧ s₂.pos = s₀.pos ∧
      (∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
          eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
            some (lo', y) → lo' < lo + 1 →
          (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
            2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
          (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
        s₂.store.read q b i = s₀.store.read q b i) ∧
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
        lo' < lo + 1 →
        pairLayout.Holds s₂.store p H.Ua (2 * (n * n) * d + 2 * n * lo')
            (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
              (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo' y)).1 ∧
          ∀ i : Fin y.k, s₂.store.read p H.Ea (n * d + lo' + i) = some
            ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
              (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo' y)).2 i) := by
  obtain ⟨hUE, -, -, -, -, -, -, hSzU, hSzE, -⟩ := el5_hne hnd
  have hSz : ∀ i, s₁.store.read p H.Sz i = s₀.store.read p H.Sz i := fun i =>
    hfr p _ i (Or.inl fun h => h.1.elim hSzU hSzE)
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s₁ = some s₂ at h
  rw [exec_seq_skip] at h
  by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
  swap
  · push Not at hy
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.2.1 lo hlo fun a y ha => hy a y ha)
    rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk (Nat.zero_le _)] at h
    change exec I (.seq (.loop _ _) .skip) _ = some s₂ at h
    rw [el5_seq_loop_zero (by simp), exec_skip] at h
    cases h
    refine ⟨hsh, hps, fun q b i hb => hfr q b i (hb.imp_right fun H' a lo' y ha hay hlt =>
      H' a lo' y ha hay (by omega)), fun a lo' y ha hay hlt =>
      hdone a lo' y ha hay (lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) ?_)⟩
    rintro rfl
    exact hy a y ha hay
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hay).1
  obtain ⟨hk1, hb⟩ := eighLoc_bounds (by omega : 1 ≤ n) hay
  rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk
    (by simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var]; omega)] at h
  change exec I (.seq (.loop _ _) .skip) _ = some s₂ at h
  rw [el5_seq_loop_one (by simp; omega)] at h
  obtain ⟨s₃, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_skip] at h
  cases h
  -- the nodes below the slot lie before it
  have hbefore : ∀ (a' : List Bool) (lo' : ℕ) (y' : EighNode K), a'.length = d →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo', y') →
      lo' < lo → lo' + y'.k ≤ lo ∧ y'.k ≤ n := by
    intro a' lo' y' ha' hay' hlt
    have hb' := eighLoc_bounds (by omega : 1 ≤ n) hay'
    have hne : a' ≠ a := by
      rintro rfl
      rw [hay] at hay'
      cases hay'
      omega
    have := eighLoc_disjoint (ha'.trans ha.symm) hne hay' hay
    omega
  have hblk : ∀ lo' k', lo' + k' ≤ lo → k' ≤ n →
      2 * n * lo' + 2 * (k' * k') ≤ 2 * n * lo := fun lo' k' h1 h2 => by
    nlinarith [Nat.mul_le_mul_right k' h2]
  obtain ⟨N1, N2, N3, N4⟩ := el5_node hmm p n ℓ₀ F d D (by omega) hd H t ha hay hnd htH ht0 ht1
    hrec hout (s₁ := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) (fun q b i hb' => by
      refine hfr q b i (hb'.imp_right fun ⟨hU', hE'⟩ a' lo' y' ha' hay' hlt => ?_)
      obtain ⟨h1, h2⟩ := hbefore a' lo' y' ha' hay' hlt
      have := hblk lo' y'.k h1 h2
      refine ⟨?_, ?_⟩
      · by_cases hbU : b = H.Ua
        · exact Or.inr (Or.inr (by have := hU' hbU; omega))
        · exact Or.inl hbU
      · by_cases hbE : b = H.Ea
        · exact Or.inr (Or.inr (by have := hE' hbE; omega))
        · exact Or.inl hbE) h₁
  have hWin : ∀ b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) →
      (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
        2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ i) ∧
      (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + y.k ≤ i) := by
    intro b i hb'
    have hlt : 2 * n * lo + 2 * (y.k * y.k) ≤ 2 * (n * n) := by
      nlinarith [Nat.mul_le_mul_left n hb]
    refine ⟨?_, ?_⟩
    · by_cases hbU : b = H.Ua
      · subst hbU
        refine Or.inr ?_
        by_contra hc
        refine hb' ⟨Or.inl rfl, Or.inl ⟨Or.inr (Or.inl rfl), by omega, ?_⟩⟩
        rw [Nat.mul_succ]
        omega
      · exact Or.inl hbU
    · by_cases hbE : b = H.Ea
      · subst hbE
        refine Or.inr ?_
        by_contra hc
        refine hb' ⟨Or.inr rfl, Or.inr (Or.inl ⟨Or.inl rfl, by omega, ?_⟩)⟩
        rw [Nat.mul_succ]
        omega
      · exact Or.inl hbE
  refine ⟨N1.trans hsh, N2.trans hps, fun q b i hb' => ?_, fun a' lo' y' ha' hay' hlt => ?_⟩
  · have hW : (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
        2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ i) ∧
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + y.k ≤ i) := by
      rcases hb' with hb' | hb'
      · exact hWin b i hb'
      · exact hb' a lo y ha hay (Nat.lt_succ_self lo)
    rw [N4 q b i hW.1 hW.2]
    exact hfr q b i (hb'.imp_right fun H' a lo' y ha hay hlt => H' a lo' y ha hay (by omega))
  · by_cases hll : lo' = lo
    · subst hll
      have haa : a' = a := by
        by_contra hne
        have := eighLoc_disjoint (ha'.trans ha.symm) hne hay' hay
        have := (eighLoc_bounds (by omega : 1 ≤ n) hay').1
        omega
      subst haa
      rw [hay] at hay'
      cases hay'
      exact N3
    · have hlt' : lo' < lo := by omega
      obtain ⟨hU', hE'⟩ := hdone a' lo' y' ha' hay' hlt'
      obtain ⟨h1, h2⟩ := hbefore a' lo' y' ha' hay' hlt'
      have := hblk lo' y'.k h1 h2
      refine ⟨hU'.of_forall_read_eq fun i hi hi' => N4 p _ i (Or.inr (Or.inl ?_))
        (Or.inl hUE), fun i => (N4 p _ _ (Or.inl (Ne.symm hUE))
          (Or.inr (Or.inl (by omega)))).trans (hE' i)⟩
      simp only [pairLayout] at hi'
      have : y'.k * y'.k * 2 = 2 * (y'.k * y'.k) := by ring
      omega

omit [AddMonoid C] [Inhabited K] in
/-- The level encoding reads only the arenas: it transfers to a store that reads as `s` there. -/
private theorem el5_transfer {H : EighArenas} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ D d : ℕ} {R₀ β : K} {root : EighNode K}
    {sem : ScalarSem P K} (hs : ∀ q b i, b ∈ H.handles → s'.read q b i = s.read q b i) :
    (H.LevelHolds sem s p M n F ℓ₀ R₀ β root d → H.LevelHolds sem s' p M n F ℓ₀ R₀ β root d) ∧
      (H.RecordHolds sem s p M n F R₀ β root d → H.RecordHolds sem s' p M n F R₀ β root d) ∧
      (H.OutHolds s p M n F D R₀ β root d → H.OutHolds s' p M n F D R₀ β root d) := by
  have hm : ∀ {b}, b ∈ [H.Ma, H.Ua, H.Qa, H.Ea, H.Sz, H.Kd, H.Kp, H.Lv] → b ∈ H.handles :=
    fun h => h
  have hR : ∀ {b i k}, b ∈ H.handles → ReadsIdx sem s p b i k → ReadsIdx sem s' p b i k :=
    fun hb h => by unfold ReadsIdx at h ⊢; rw [hs p _ _ hb]; exact h
  have hH : ∀ {b off l m} {Y : Matrix (Fin l) (Fin m) (K × K)}, b ∈ H.handles →
      pairLayout.Holds s p b off Y → pairLayout.Holds s' p b off Y :=
    fun hb h => h.of_forall_read_eq fun i _ _ => hs p _ i hb
  refine ⟨fun h => ⟨fun a lo y ha hay => ?_, fun lo hlo hno => ?_, ?_, ?_⟩,
    fun h a lo y ha hay hk => ?_, fun h a lo y ha hay => ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 a lo y ha hay
    exact ⟨hR (hm (by simp)) h1, hH (hm (by simp)) h2⟩
  · exact hR (hm (by simp)) (h.2.1 lo hlo hno)
  · rw [hs p _ _ (hm (by simp))]; exact h.2.2.1
  · rw [hs p _ _ (hm (by simp))]; exact h.2.2.2
  · have := h a lo y ha hay hk
    split at this
    · obtain ⟨h1, h2, h3⟩ := this
      exact ⟨hR (hm (by simp)) h1, hH (hm (by simp)) h2,
        fun i => (hs p _ _ (hm (by simp))).trans (h3 i)⟩
    · exact hR (hm (by simp)) this
    · obtain ⟨h1, h2, h3, h4⟩ := this
      exact ⟨hR (hm (by simp)) h1, hR (hm (by simp)) h2, hH (hm (by simp)) h3,
        hH (hm (by simp)) h4⟩
  · obtain ⟨h1, h2⟩ := h a lo y ha hay
    exact ⟨hH (hm (by simp)) h1, fun i => (hs p _ _ (hm (by simp))).trans (h2 i)⟩

/-- **One level of the upward pass**: if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, under exact integer literals up to $n + 4$ and the exact floor conversion, a successful run
of `NLAlib.eighUpLevel` at depth $d < D$ from a state whose arenas hold the nodes of depth $d$
(their sizes), the records of depth $d$ and the outputs of depth $d + 1$, with the window of depth
$d$ in its cell and the stored $\mathrm{fl}(2)$ in `two`, ends with the outputs of depth $d$
(`NLAlib.EighArenas.OutHolds` at $d$, budget $D - d$); every cell outside the output and eigenvalue
arenas at depth $d$ is unchanged, the store shape and the tape positions too. No printed source.
Proof: the loop over the slots with the invariant "the slots below $lo$ are done"; at a node $y$ the
binder reads its kind (`NLAlib.EighArenas.RecordHolds`), and `NLAlib.eighAux` at budget
$D - d = (D - d - 1) + 1$ unfolds at the node (`Nat.sub_add_cancel`): a leaf's output is already
stored; a one-child node copies its child's $\mathbf{U}$ (the pilot's
`NLAlib.Computation.holds_of_exec_zcopy` after `NLAlib.Computation.exec_zcopy_congr`) and adds
$\pm\sigma$; a split reads $k_+$ and runs the two kernel calls into the column blocks of the node's
output (`NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some`, pilot), which is
`Matrix.fromCols` reindexed by `finSumFinEquiv` packed column-major (the first $k_+$ columns are the
first $2kk_+$ words), and the eigenvalues by the two loops; the children's outputs are those of
`NLAlib.EighArenas.OutHolds` at $d + 1$ through `NLAlib.eighSlotTree_append_of_eighLoc` and
`NLAlib.eighLoc_append_singleton`. L, about 180 lines (split the split case into a private lemma).
-/
theorem holds_of_exec_eighUpLevel {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {dec : P → K → ℝ} (p : P) (n ℓ₀ F d D : ℕ) (hd : d < D)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {two : Cell ℕ ℕ} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (htwo : two.buf ∉ H.handles)
    (htwov : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (h : exec I (eighUpLevel p mm (.const n) (.const d) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
      two).run st = some st') :
    H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have hltH : ∀ b ∈ H.handles, b < st.store.size := by
    simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv]
  have htH : st.store.size ∉ H.handles := fun hm => absurd (hltH _ hm) (lt_irrefl _)
  obtain ⟨z2, hz2, -⟩ := hlit p 2 (by omega)
  have htwo' : st.store.read p two.buf two.idx.eval = some z2 := htwov.trans hz2
  have ltwo := Store.lt_size_of_read_eq_some htwo'
  set M := eighTapeMachine I p mmR qrR with hM
  -- the scope and the scratch cells
  change exec I (.seq (.alloc p _ _) .skip) st = some st' at h
  rw [exec_seq_skip, exec_alloc] at h
  obtain ⟨s₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
  change exec I (.seq (.instr _) (.seq (.instr _) (.seq (.loop _ _) .skip))) _ = some s₁ at h₁
  rw [exec_seq] at h₁
  obtain ⟨σa, ha, h₁⟩ := Option.bind_eq_some_iff.mp h₁
  rw [exec_seq] at h₁
  obtain ⟨σb, hb, h₁⟩ := Option.bind_eq_some_iff.mp h₁
  rw [exec_seq_skip] at h₁
  rw [exec_instr] at ha hb
  obtain ⟨ra, hra, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨rb, hrb, rfl⟩ := Option.map_eq_some_iff.mp hb
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hra hrb
  obtain ⟨xR, hxR, x2, hx2, v0, hv0, wa, hwa, rfl⟩ := hra
  obtain ⟨x0, hx0, v1, hv1, wb, hwb, rfl⟩ := hrb
  set t := st.store.size with ht
  have hP : ∀ {q : P} {b i : ℕ}, b < t →
      Store.read (st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)) q b i =
        st.store.read q b i := fun hb => Store.read_push_of_lt hb
  have hrd₀ : ∀ q b i, b < t → wb.read q b i = st.store.read q b i := fun q b i hb => by
    rw [Store.read_of_write_eq_some_of_ne hwb (Or.inl (Nat.ne_of_lt hb)),
      Store.read_of_write_eq_some_of_ne hwa (Or.inl (Nat.ne_of_lt hb)), hP hb]
  rw [hP (hltH _ (by simp [EighArenas.handles]))] at hxR
  rw [show (2 * IExp.const d : IExp ℕ).eval = 2 * d from rfl, hlev.2.2.1] at hxR
  cases hxR
  rw [hP ltwo, htwo'] at hx2
  cases hx2
  rw [Store.read_of_write_eq_some hwa] at hx0
  cases hx0
  have hv0' : I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1 z2 = some v0 := hv0
  rw [IExp.eval_zero] at hwa
  rw [IExp.eval_one] at hwb
  dsimp only at hwb ⊢
  have ht0 : wb.read p t 0 = some (M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2)) := by
    rw [Store.read_of_write_eq_some_of_ne hwb (Or.inr (by decide)),
      Store.read_of_write_eq_some hwa]
    change some v0 = some ((I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1
      ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)
    rw [hz2, Option.getD_some, hv0', Option.getD_some]
  have ht1 : wb.read p t 1 = some (M.neg (M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2))) := by
    rw [Store.read_of_write_eq_some hwb]
    change some v1 = some ((I.sem.un p .neg ((I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1
      ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)).getD default)
    rw [hz2, Option.getD_some, hv0', Option.getD_some, hv1, Option.getD_some]
  obtain ⟨T1, T2, T3⟩ := el5_transfer (H := H) (s := st.store) (s' := wb) (p := p) (M := M)
    (n := n) (F := F) (ℓ₀ := ℓ₀) (D := D) (d := d) (R₀ := R₀) (β := β)
    (root := ⟨n, A, R₀, ε, ℓ₀⟩) (sem := I.sem) fun q b i hb => hrd₀ q b i (hltH b hb)
  obtain ⟨T1', T2', T3'⟩ := el5_transfer (H := H) (s := st.store) (s' := wb) (p := p) (M := M)
    (n := n) (F := F) (ℓ₀ := ℓ₀) (D := D) (d := d + 1) (R₀ := R₀) (β := β)
    (root := ⟨n, A, R₀, ε, ℓ₀⟩) (sem := I.sem) fun q b i hb => hrd₀ q b i (hltH b hb)
  refine (fun L => ?_) (forall_of_exec_loop_eq_some I (n := .const n)
    (fun lo (s : St P K C) => s.store.shape = wb.shape ∧ s.pos = st.pos ∧
      (∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) → lo' < lo →
          (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
            2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
          (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
        s.store.read q b i = wb.read q b i) ∧
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
        eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) → lo' < lo →
        pairLayout.Holds s.store p H.Ua (2 * (n * n) * d + 2 * n * lo')
            (eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).1 ∧
          ∀ i : Fin y.k, s.store.read p H.Ea (n * d + lo' + i) = some
            ((eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).2 i))
    ?_ ?_ h₁)
  rotate_left
  · exact ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · exact fun lo hlo s₂ s₃ ⟨hsh, hps, hfr, hdone⟩ hex =>
      el5_step hmm p n ℓ₀ F d D hd H t (s₀ := { st with store := wb }) (by simpa using hlo) hnd
        htH ht0 ht1 (T1 hlev) (T2 hrec) (T3' hout) hsh hps hfr hdone hex
  obtain ⟨Lsh, Lps, Lfr, Ldone⟩ := L
  simp only [IExp.eval_const] at Ldone
  have hs₁ : s₁.store.size = t + 1 := by
    have := congrArg Array.size Lsh
    rw [Store.shape_of_write_eq_some hwb, Store.shape_of_write_eq_some hwa] at this
    simpa [Store.shape] using this
  have hpop : ∀ {q : P} {b i : ℕ}, b < t → Store.read s₁.store.pop q b i = s₁.store.read q b i :=
    fun hb => Store.read_pop_of_lt (by omega)
  refine ⟨fun a lo y ha hay => ?_, fun q b i hb => ?_, ?_, Lps⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hy0 : y.k = 0 := by
        cases a with
        | nil => cases hay; rfl
        | cons b a => simp [eighLoc, eighStep] at hay
      have hk : ∀ i : Fin y.k, False := fun i => absurd i.isLt (by omega)
      exact ⟨fun i => (hk i).elim, fun i => (hk i).elim⟩
    have hb := eighLoc_bounds hn hay
    obtain ⟨hU, hE⟩ := Ldone a lo y ha hay (by omega)
    exact ⟨hU.of_forall_read_eq fun i _ _ => hpop (hltH _ (by simp [EighArenas.handles])),
      fun i => (hpop (hltH _ (by simp [EighArenas.handles]))).trans (hE i)⟩
  · by_cases hbt : b < t
    · exact (hpop hbt).trans ((Lfr q b i (Or.inl hb)).trans (hrd₀ q b i hbt))
    · have hsz' : (Array.pop s₁.store).size = t := by simp [hs₁]
      exact (Store.read_eq_none_of_size_le (by omega)).trans
        (Store.read_eq_none_of_size_le (by omega)).symm
  · rw [Store.shape_pop, Lsh, Store.shape_of_write_eq_some hwb, Store.shape_of_write_eq_some hwa]
    simp [Store.shape]

omit [AddMonoid C] in
/-- A product kernel call on held matrices succeeds when the output block fits. -/
private theorem el6_exists_kcall {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) {l m n : ℕ} {a b c : ℕ × ℕ} {s : Store P K} {A : Matrix (Fin l) (Fin m) (K × K)}
    {B : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds s p a.1 a.2 A)
    (hB : pairLayout.Holds s p b.1 b.2 B)
    (hca : blockDisjoint (c.1, c.2, n * l * 2) (a.1, a.2, m * l * 2) = true)
    (hcb : blockDisjoint (c.1, c.2, n * l * 2) (b.1, b.2, n * m * 2) = true)
    {len : ℕ} (hc : s.shape[c.1]? = some (p, len)) (hlen : c.2 + n * l * 2 ≤ len) :
    ∃ s', I.kcallStore mm p [l, m, n] [a, b] [c] s = some s' := by
  rw [hmm.kcallStore_eq p ((EntryLayout.holds_iff_readBlock_eq_some pairLayout s p _ _ A).mp hA)
    ((EntryLayout.holds_iff_readBlock_eq_some pairLayout s p _ _ B).mp hB) hca hcb]
  exact Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi => ⟨len, hc, by
    rw [EntryLayout.size_toArray] at hi
    change i < n * l * 2 at hi
    omega⟩

omit [Inhabited K] in
/-- A loop of binary operations `Y[f w] ← Y[g w] ∘ c` succeeds when the written cells fit, the
read cells are initialised and never written, and the operation always succeeds. -/
private theorem el6_binLoop {p : P} {op : BinOp} {m : IExp ℕ} {Y : ℕ} {c : Cell ℕ ℕ}
    {f g : ℕ → IExp ℕ} {st : St P K C} {len : ℕ} (hYc : c.buf ≠ Y)
    (hfg : ∀ w < m.eval, ∀ w' < m.eval, (f w).eval ≠ (g w').eval)
    (hY : st.store.shape[Y]? = some (p, len)) (hf : ∀ w < m.eval, (f w).eval < len)
    (hg : ∀ w < m.eval, ∃ x, st.store.read p Y (g w).eval = some x)
    (hc : ∃ z, st.store.read p c.buf c.idx.eval = some z)
    (hop : ∀ x z, ∃ v, I.sem.bin p op x z = some v) :
    ∃ st', exec I (.loop m fun w => .seq (.instr (.bin p op ⟨Y, f w⟩ ⟨Y, g w⟩ c)) .skip) st =
      some st' := by
  refine (exists_exec_loop_eq_some_of_forall (I := I)
    (fun w s => s.store.shape = st.store.shape ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w' < w, (f w').eval ≠ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, fun _ _ _ _ => rfl⟩ ?_).imp fun _ h => h.1
  rintro w hw s ⟨hsh, hrd⟩
  obtain ⟨x, hx⟩ := hg w hw
  obtain ⟨z, hz⟩ := hc
  obtain ⟨v, hv⟩ := hop x z
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := s.store) v
    (hsh ▸ hY) (hf w hw)
  refine ⟨_, (exec_seq_instr_bin I (x := ⟨Y, g w⟩) (y := c)
    ((hrd p _ _ (Or.inr fun w' hw' => hfg w' (by omega) w hw)).trans hx)
    ((hrd p _ _ (Or.inl hYc)).trans hz) hv hs').trans (exec_skip I _), ?_, fun q b i hb => ?_⟩
  · exact (Store.shape_of_write_eq_some hs').trans hsh
  · rw [Store.read_of_write_eq_some_of_ne hs' ?_]
    · exact hrd q b i (hb.imp_right fun h w' hw' => h w' (by omega))
    · exact hb.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

/-- The branch of a one-child node in the upward pass succeeds. -/
private theorem el6_shift_ex (p : P) (n d D lo k : ℕ) (hd : d < D) (H : EighArenas)
    (tc : Cell ℕ ℕ) {s : St P K C} (hk : lo + k ≤ n) (hUE : H.Ua ≠ H.Ea) (htc : tc.buf ≠ H.Ea)
    (htcU : tc.buf ≠ H.Ua) {U : Matrix (Fin k) (Fin k) (K × K)}
    (hUs : s.store.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)))
    (hEs : s.store.shape[H.Ea]? = some (p, n * (D + 1)))
    (hU : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U)
    (hE : ∀ i < k, ∃ x, s.store.read p H.Ea (n * (d + 1) + lo + i) = some x)
    (hσ : ∃ σ, s.store.read p tc.buf tc.idx.eval = some σ)
    (hop : ∀ x z, ∃ v, I.sem.bin p .add x z = some v) :
    ∃ s', exec I (do
        zcopy (ι := ι) p (IExp.var k) (IExp.var k) H.Ua
          (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))
          H.Ua (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
        forRange (IExp.var k) fun i => ins (.bin p .add
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
          tc)).run s = some s' := by
  rw [exec_run_bind I (b := zcopy (ι := ι) p (IExp.var k) (IExp.var k) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))) (fun _ => rfl), exec_zcopy_congr]
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  have hU' : pairLayout.Holds s.store p H.Ua
      (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)).eval U := by
    simpa [eighBlockOff, Nat.mul_succ] using hU
  have hXY : blockDisjoint (H.Ua, (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)).eval,
      2 * (k * k)) (H.Ua, (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)).eval,
      2 * (k * k)) = true :=
    el5_bd2 (Or.inl (by
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var, IExp.eval_ofNat]
      rw [Nat.mul_succ]; omega))
  obtain ⟨s₁, hz⟩ := exists_exec_zcopy (I := I) p k k (st := s) hU' hXY ⟨_, hUs, by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat]
    have : lo * n + k * n ≤ n * n := by nlinarith
    nlinarith⟩
  obtain ⟨-, hfr₁, hsh₁, -⟩ := holds_of_exec_zcopy p k k hU' hXY hz
  rw [IExp.eval_var, hz, Option.bind_some]
  change ∃ s', exec I (.seq (.loop _ _) .skip) _ = _
  simp only [exec_seq_skip]
  refine el6_binLoop htc ?_ (hsh₁ ▸ hEs) ?_ ?_ ?_ hop
  · intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw hw' ⊢
    rw [Nat.mul_succ]; omega
  · intro w hw
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at hw ⊢
    have := Nat.mul_le_mul_left n hd
    rw [Nat.mul_succ] at this ⊢; omega
  · intro w hw
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw ⊢
    rw [hfr₁ p _ _ (el5_bd (Or.inl (Ne.symm hUE)))]
    obtain ⟨x, hx⟩ := hE w hw
    exact ⟨x, by rw [← hx, Nat.mul_succ]⟩
  · obtain ⟨σ, hσ⟩ := hσ
    exact ⟨σ, by rw [hfr₁ p _ _ (el5_bd (Or.inl htcU))]; exact hσ⟩

/-- The branch of a split in the upward pass succeeds. -/
private theorem el6_split_ex {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n d D lo k kp t : ℕ) (hd : d < D) (H : EighArenas) {s : St P K C} (hk : lo + k ≤ n)
    (hkp : kp < k) (hUE : H.Ua ≠ H.Ea) (hUQ : H.Ua ≠ H.Qa) (htE : t ≠ H.Ea) (htU : t ≠ H.Ua)
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Up : Matrix (Fin kp) (Fin kp) (K × K)} {Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    (hUs : s.store.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)))
    (hEs : s.store.shape[H.Ea]? = some (p, n * (D + 1)))
    (hQp : pairLayout.Holds s.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds s.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (hUp : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up)
    (hUm : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um)
    (hEp : ∀ j < kp, ∃ x, s.store.read p H.Ea (n * (d + 1) + lo + j) = some x)
    (hEm : ∀ j < k - kp, ∃ x, s.store.read p H.Ea (n * (d + 1) + (lo + kp) + j) = some x)
    (hσ : ∃ σ, s.store.read p t 0 = some σ)
    (hadd : ∀ x z, ∃ v, I.sem.bin p .add x z = some v)
    (hsub : ∀ x z, ∃ v, I.sem.bin p .sub x z = some v) :
    ∃ s', exec I (do
        let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
        stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
          [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
          [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
        stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp, IExp.var k - IExp.var kp]
          [(H.Qa, qo + 2 * (IExp.var k * IExp.var kp)),
            (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo + IExp.var kp))]
          [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
            2 * (IExp.var k * IExp.var kp))])
        forRange (IExp.var kp) fun j => ins (.bin p .add
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩ ⟨t, 0⟩)
        forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp + IExp.var j⟩
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
            IExp.var j⟩ ⟨t, 0⟩)).run s = some s' := by
  change ∃ s', exec I (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.loop _ _) (.seq (.loop _ _) .skip)))) s = some s'
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  have hkpk : k * kp ≤ k * k := Nat.mul_le_mul_left k hkp.le
  have hsplit : k * kp + k * (k - kp) = k * k := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hkp.le]
  have hlok : lo * n + k * n ≤ n * n := by nlinarith
  have hc1 : (k - kp) * k = k * (k - kp) := Nat.mul_comm _ _
  have hc2 : kp * k = k * kp := Nat.mul_comm _ _
  have hnD := Nat.mul_le_mul_left n hd
  rw [Nat.mul_succ] at hnD
  obtain ⟨u₁, hu₁⟩ := el6_exists_kcall hmm p (l := k) (m := kp) (n := kp)
    (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * lo))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo)) hQp hUp
    (el5_bd2' (Or.inl hUQ))
    (el5_bd2 (Or.inl (by rw [Nat.mul_succ]; nlinarith))) hUs
    (by dsimp only; rw [Nat.mul_succ]; nlinarith)
  obtain ⟨-, hfr₁⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p hQp hUp
    (el5_bd2' (Or.inl hUQ))
    (el5_bd2 (Or.inl (by simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith))) hu₁
  have hsh₁ := Interp.shape_of_kcallStore_eq_some hu₁
  rw [exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, eighBlockOff, IExp.eval_add, IExp.eval_mul,
    IExp.eval_const, IExp.eval_var, IExp.eval_ofNat]
  rw [hu₁, Option.map_some, Option.bind_some]
  have hQm₁ := hQm.of_forall_read_eq fun i _ _ => hfr₁ p _ i (el5_bd (Or.inl (Ne.symm hUQ)))
  have hUm₁ := hUm.of_forall_read_eq fun i hi _ => hfr₁ p _ i (el5_bd (Or.inr (Or.inr (by
    simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith))))
  obtain ⟨u₂, hu₂⟩ := el6_exists_kcall hmm p (l := k) (m := k - kp) (n := k - kp)
    (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * (lo + kp)))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))) hQm₁ hUm₁
    (el5_bd2' (Or.inl hUQ)) (el5_bd2 (Or.inl (by
      rw [Nat.mul_succ]; nlinarith))) (hsh₁ ▸ hUs)
    (by dsimp only; rw [Nat.mul_succ]; nlinarith)
  obtain ⟨-, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p hQm₁ hUm₁
    (el5_bd2' (Or.inl hUQ)) (el5_bd2 (Or.inl (by
      simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith))) hu₂
  have hsh₂ := Interp.shape_of_kcallStore_eq_some hu₂
  rw [exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, IExp.eval_add, IExp.eval_mul,
    IExp.eval_const, IExp.eval_var, IExp.eval_ofNat, IExp.eval_sub]
  rw [show I.kcallStore mm p [k, k - kp, k - kp]
      [(H.Qa, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)),
        (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * (lo + kp))]
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))] u₁ = some u₂ from hu₂,
    Option.map_some, Option.bind_some]
  have hrdE : ∀ i, u₂.read p H.Ea i = s.store.read p H.Ea i := fun i => by
    rw [hfr₂ p _ i (el5_bd (Or.inl (Ne.symm hUE))), hfr₁ p _ i (el5_bd (Or.inl (Ne.symm hUE)))]
  have hrdt : u₂.read p t 0 = s.store.read p t 0 := by
    rw [hfr₂ p _ _ (el5_bd (Or.inl htU)), hfr₁ p _ _ (el5_bd (Or.inl htU))]
  have hEs₂ : u₂.shape[H.Ea]? = some (p, n * (D + 1)) := by rw [hsh₂, hsh₁]; exact hEs
  rw [exec_seq]
  obtain ⟨s₃, h₃⟩ := el6_binLoop (I := I) (c := ⟨t, 0⟩) (Y := H.Ea)
    (st := { s with
      store := u₂
      cnt := s.cnt + I.charge (.kcall p mm [k, kp, kp]) +
        I.charge (.kcall p mm [k, k - kp, k - kp]) })
    (f := fun j => eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j)
    (g := fun j => eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j)
    (m := IExp.var kp) htE (by
      intro w hw w' hw'
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
        IExp.eval_ofNat] at hw hw' ⊢
      rw [Nat.mul_succ]; omega) hEs₂ (by
      intro w hw
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var] at hw ⊢
      rw [Nat.mul_succ]; omega) (by
      intro w hw
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
        IExp.eval_ofNat] at hw ⊢
      rw [hrdE]
      obtain ⟨x, hx⟩ := hEp w hw
      exact ⟨x, by rw [← hx, Nat.mul_succ]⟩) (by
      obtain ⟨σ, hσ⟩ := hσ
      exact ⟨σ, by rw [IExp.eval_zero, hrdt]; exact hσ⟩) hadd
  obtain ⟨hsh₃, -, -, hfr₃⟩ := el5_binLoop htE (by
      intro w hw w' hw'
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
        IExp.eval_ofNat] at hw hw' ⊢
      rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h₃
  erw [h₃]
  rw [Option.bind_some, exec_seq_skip]
  refine el6_binLoop htE ?_ (hsh₃ ▸ hEs₂) ?_ ?_ ?_ hsub
  · intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat, IExp.eval_sub] at hw hw' ⊢
    rw [Nat.mul_succ]; omega
  · intro w hw
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_sub] at hw ⊢
    rw [Nat.mul_succ]; omega
  · intro w hw
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat, IExp.eval_sub] at hw ⊢
    rw [hfr₃ p _ _ (Or.inr fun w' hw' => by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var] at hw' ⊢
      rw [Nat.mul_succ]; omega), hrdE]
    obtain ⟨x, hx⟩ := hEm w hw
    exact ⟨x, by rw [← hx, Nat.mul_succ]; congr 1; omega⟩
  · obtain ⟨σ, hσ⟩ := hσ
    exact ⟨σ, by rw [hfr₃ p _ _ (Or.inl htE), IExp.eval_zero, hrdt]; exact hσ⟩

/-- **One node of the upward pass succeeds** (hypotheses as for its run). -/
private theorem el6_node_ex {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n ℓ₀ F d D : ℕ) (hn : 1 ≤ n) (hd : d < D) (H : EighArenas) (t : ℕ) {s₀ s₁ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {a : List Bool} {lo : ℕ}
    {y : EighNode K} (ha : a.length = d)
    (hay : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
      some (lo, y))
    (hnd : H.handles.Nodup) (htH : t ∉ H.handles)
    (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (ht1 : s₀.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
      ((eighTapeMachine I p mmR qrR).div (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
        ((eighTapeMachine I p mmR qrR).ofNat 2))))
    (hrec : H.RecordHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (hR : ∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ((b = H.Ua → 2 * (n * n) * d + 2 * n * lo ≤ i ∧
            i < 2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k)) ∧
          (b = H.Ea → n * d + lo ≤ i ∧ i < n * d + lo + y.k))) →
        s₁.store.read q b i = s₀.store.read q b i)
    (hUs : s₁.store.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)))
    (hEs : s₁.store.shape[H.Ea]? = some (p, n * (D + 1)))
    (hadd : ∀ x z, ∃ v, I.sem.bin p .add x z = some v)
    (hsub : ∀ x z, ∃ v, I.sem.bin p .sub x z = some v) :
    ∃ s₂, exec I (Builder.bindIdx (ι := ι) p
      ⟨H.Kd, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩ 4 fun c => do
        eighWhen (eighEqInd (IExp.var c) 2) do
          zcopy p (IExp.var y.k) (IExp.var y.k) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
          forRange (IExp.var y.k) fun i => ins (.bin p .add
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
            ⟨t, 0⟩)
        eighWhen (eighEqInd (IExp.var c) 3) do
          zcopy p (IExp.var y.k) (IExp.var y.k) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
          forRange (IExp.var y.k) fun i => ins (.bin p .add
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
            ⟨t, 1⟩)
        eighWhen (eighEqInd (IExp.var c) 4) <|
          Builder.bindIdx p ⟨H.Kp, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
            (IExp.var y.k) fun kp => do
            let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
            stmt (.kcall mm p [IExp.var y.k, IExp.var kp, IExp.var kp]
              [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
              [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
            stmt (.kcall mm p [IExp.var y.k, IExp.var y.k - IExp.var kp,
                IExp.var y.k - IExp.var kp]
              [(H.Qa, qo + 2 * (IExp.var y.k * IExp.var kp)),
                (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1)
                  (IExp.var lo + IExp.var kp))]
              [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
                2 * (IExp.var y.k * IExp.var kp))])
            forRange (IExp.var kp) fun j => ins (.bin p .add
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩
              ⟨t, 0⟩)
            forRange (IExp.var y.k - IExp.var kp) fun j => ins (.bin p .sub
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp +
                IExp.var j⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
                IExp.var j⟩ ⟨t, 0⟩)).run s₁ = some s₂ := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn hay
  obtain ⟨hUE, hUQ, hKdU, hKdE, hKpU, hKpE, hQE, -⟩ := el5_hne hnd
  have htU : t ≠ H.Ua := fun e => htH (e ▸ by simp [EighArenas.handles])
  have htE : t ≠ H.Ea := fun e => htH (e ▸ by simp [EighArenas.handles])
  have hRo : ∀ q b i, b ≠ H.Ua → b ≠ H.Ea → s₁.store.read q b i = s₀.store.read q b i :=
    fun q b i h1 h2 => hR q b i (Or.inl fun h => h.1.elim h1 h2)
  have hRU1 : ∀ q i, 2 * (n * n) * (d + 1) ≤ i → s₁.store.read q H.Ua i = s₀.store.read q H.Ua i :=
    fun q i hi => hR q _ i (Or.inl fun ⟨_, hc⟩ => by have := el5_lc_Ua hnd hc; omega)
  have hRE1 : ∀ q i, n * (d + 1) ≤ i → s₁.store.read q H.Ea i = s₀.store.read q H.Ea i :=
    fun q i hi => hR q _ i (Or.inl fun ⟨_, hc⟩ => by have := el5_lc_Ea hnd hc; omega)
  have hr := hrec a lo y ha hay hk1
  change ∃ s₂, exec I (.seq (.bindIdx _ _ _ _) .skip) s₁ = some s₂
  rw [exec_seq_skip]
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    rw [hs] at hr
    obtain ⟨hkd, -, -⟩ := hr
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hkd
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk (by decide)]
    change ∃ s₂, exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _
    rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, exec_skip]
    exact ⟨_, rfl⟩
  | shift b A' σ' =>
    rw [hs] at hr
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hr
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk (by split <;> decide)]
    have hch : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [b]) = some (lo,
        ⟨y.k, A', (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
          y.ℓ + 1⟩) := by
      rw [eighLoc_append_singleton, hay]
      simp [eighLoc, ha, hs]
    obtain ⟨hUc, hEc⟩ := hout (a ++ [b]) lo _ (by simp [ha]) hch
    have hUc' := hUc.of_forall_read_eq (s' := s₁.store) fun i hi _ => hRU1 p i (by omega)
    have hEc' : ∀ i < y.k, ∃ x, s₁.store.read p H.Ea (n * (d + 1) + lo + i) = some x :=
      fun i hi => ⟨_, (hRE1 p _ (by omega)).trans (hEc ⟨i, hi⟩)⟩
    change ∃ s₂, exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _
    cases b
    · rw [el5_seq_loop_zero rfl, el5_seq_loop_one rfl]
      obtain ⟨s₃, h₃⟩ := el6_shift_ex p n d D lo y.k hd H ⟨t, 1⟩ hkn hUE htE htU
        (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) hUs hEs hUc' hEc'
        ⟨_, (hRo p _ _ htU htE).trans ht1⟩ hadd
      erw [h₃]
      rw [Option.bind_some, el5_seq_loop_zero rfl, exec_skip]
      exact ⟨_, rfl⟩
    · rw [el5_seq_loop_one rfl]
      obtain ⟨s₃, h₃⟩ := el6_shift_ex p n d D lo y.k hd H ⟨t, 0⟩ hkn hUE htE htU
        (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) hUs hEs hUc' hEc'
        ⟨_, (hRo p _ _ htU htE).trans ht0⟩ hadd
      erw [h₃]
      rw [Option.bind_some, el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, exec_skip]
      exact ⟨_, rfl⟩
  | split kp hkp Qp Qm Ap Am σ' =>
    rw [hs] at hr
    obtain ⟨-, hkp0, hkpk⟩ := el5_eighStep_split hs
    obtain ⟨hkd, hkpr, hQp, hQm⟩ := hr
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hkd
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk (by decide)]
    change ∃ s₂, exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _
    rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, el5_seq_loop_one rfl]
    obtain ⟨v', hv', hk'⟩ := Option.bind_eq_some_iff.mp hkpr
    have hchp : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [true]) = some (lo,
        ⟨kp, Ap, (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
          y.ℓ + 1⟩) := by
      rw [eighLoc_append_singleton, hay]
      simp [eighLoc, ha, hs]
    have hchm : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [false]) = some (lo + kp,
        ⟨y.k - kp, Am, (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
          y.ℓ + 1⟩) := by
      rw [eighLoc_append_singleton, hay]
      simp [eighLoc, ha, hs]
    obtain ⟨hUp, hEp⟩ := hout (a ++ [true]) lo _ (by simp [ha]) hchp
    obtain ⟨hUm, hEm⟩ := hout (a ++ [false]) (lo + kp) _ (by simp [ha]) hchm
    obtain ⟨s₃, h₃⟩ := el6_split_ex hmm p n d D lo y.k kp t hd H hkn hkpk hUE hUQ htE htU
      (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) + I.charge (.toNat p) }) hUs hEs
      (hQp.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
      (hQm.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
      (hUp.of_forall_read_eq fun i hi _ => hRU1 p i (by omega))
      (hUm.of_forall_read_eq fun i hi _ => hRU1 p i (by nlinarith))
      (fun j hj => ⟨_, (hRE1 p _ (by omega)).trans (hEp ⟨j, hj⟩)⟩)
      (fun j hj => ⟨_, (hRE1 p _ (by omega)).trans (hEm ⟨j, hj⟩)⟩)
      ⟨_, (hRo p _ _ htU htE).trans ht0⟩ hadd hsub
    refine ⟨s₃, ?_⟩
    change (exec I (.seq (.bindIdx _ _ _ _) .skip) _).bind _ = _
    rw [exec_seq_skip, exec_bindIdx_of_read I ((hRo p _ _ hKpU hKpE).trans hv') hk'
      (by exact hkp)]
    erw [h₃]
    rfl

/-- **One slot of the upward pass succeeds** (hypotheses as for its run). -/
private theorem el6_step_ex {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (H : EighArenas) (t : ℕ) {s₀ s₁ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {lo : ℕ} (hlo : lo < n)
    (hnd : H.handles.Nodup) (htH : t ∉ H.handles)
    (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (ht1 : s₀.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
      ((eighTapeMachine I p mmR qrR).div (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
        ((eighTapeMachine I p mmR qrR).ofNat 2))))
    (hlev : H.LevelHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (hfr : ∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
          eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
            some (lo', y) → lo' < lo →
          (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
            2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
          (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
        s₁.store.read q b i = s₀.store.read q b i)
    (hUs : s₁.store.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)))
    (hEs : s₁.store.shape[H.Ea]? = some (p, n * (D + 1)))
    (hadd : ∀ x z, ∃ v, I.sem.bin p .add x z = some v)
    (hsub : ∀ x z, ∃ v, I.sem.bin p .sub x z = some v) :
    ∃ s₂, exec I (Builder.bindIdx (ι := ι) p
      ⟨H.Sz, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
      (IExp.const n - IExp.var lo) fun k => eighWhen (IExp.var k) <| Builder.bindIdx p
        ⟨H.Kd, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩ 4 fun c => do
          eighWhen (eighEqInd (IExp.var c) 2) do
            zcopy p (IExp.var k) (IExp.var k) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
            forRange (IExp.var k) fun i => ins (.bin p .add
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
              ⟨t, 0⟩)
          eighWhen (eighEqInd (IExp.var c) 3) do
            zcopy p (IExp.var k) (IExp.var k) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
            forRange (IExp.var k) fun i => ins (.bin p .add
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
              ⟨t, 1⟩)
          eighWhen (eighEqInd (IExp.var c) 4) <|
            Builder.bindIdx p ⟨H.Kp, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
              (IExp.var k) fun kp => do
              let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
              stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
                [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
                [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
              stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp,
                  IExp.var k - IExp.var kp]
                [(H.Qa, qo + 2 * (IExp.var k * IExp.var kp)),
                  (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1)
                    (IExp.var lo + IExp.var kp))]
                [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
                  2 * (IExp.var k * IExp.var kp))])
              forRange (IExp.var kp) fun j => ins (.bin p .add
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩
                ⟨t, 0⟩)
              forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp +
                  IExp.var j⟩
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
                  IExp.var j⟩ ⟨t, 0⟩)).run s₁ = some s₂ := by
  obtain ⟨hUE, -, -, -, -, -, -, hSzU, hSzE, -⟩ := el5_hne hnd
  have hSz : ∀ i, s₁.store.read p H.Sz i = s₀.store.read p H.Sz i := fun i =>
    hfr p _ i (Or.inl fun h => h.1.elim hSzU hSzE)
  change ∃ s₂, exec I (.seq (.bindIdx _ _ _ _) .skip) s₁ = some s₂
  rw [exec_seq_skip]
  by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
  swap
  · push Not at hy
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.2.1 lo hlo fun a y ha => hy a y ha)
    rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk (Nat.zero_le _)]
    change ∃ s₂, exec I (.seq (.loop _ _) .skip) _ = some s₂
    rw [el5_seq_loop_zero (by simp), exec_skip]
    exact ⟨_, rfl⟩
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hay).1
  obtain ⟨hk1, hb⟩ := eighLoc_bounds (by omega : 1 ≤ n) hay
  rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk
    (by simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var]; omega)]
  change ∃ s₂, exec I (.seq (.loop _ _) .skip) _ = some s₂
  rw [el5_seq_loop_one (by simp; omega)]
  have hbefore : ∀ (a' : List Bool) (lo' : ℕ) (y' : EighNode K), a'.length = d →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo', y') →
      lo' < lo → lo' + y'.k ≤ lo ∧ y'.k ≤ n := by
    intro a' lo' y' ha' hay' hlt
    have hb' := eighLoc_bounds (by omega : 1 ≤ n) hay'
    have hne : a' ≠ a := by
      rintro rfl
      rw [hay] at hay'
      cases hay'
      omega
    have := eighLoc_disjoint (ha'.trans ha.symm) hne hay' hay
    omega
  have hblk : ∀ lo' k', lo' + k' ≤ lo → k' ≤ n →
      2 * n * lo' + 2 * (k' * k') ≤ 2 * n * lo := fun lo' k' h1 h2 => by
    nlinarith [Nat.mul_le_mul_right k' h2]
  obtain ⟨s₃, h₃⟩ := el6_node_ex hmm p n ℓ₀ F d D (by omega) hd H t ha hay hnd htH ht0 ht1
    hrec hout (s₁ := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) (fun q b i hb' => by
      refine hfr q b i (hb'.imp_right fun ⟨hU', hE'⟩ a' lo' y' ha' hay' hlt => ?_)
      obtain ⟨h1, h2⟩ := hbefore a' lo' y' ha' hay' hlt
      have := hblk lo' y'.k h1 h2
      refine ⟨?_, ?_⟩
      · by_cases hbU : b = H.Ua
        · exact Or.inr (Or.inr (by have := hU' hbU; omega))
        · exact Or.inl hbU
      · by_cases hbE : b = H.Ea
        · exact Or.inr (Or.inr (by have := hE' hbE; omega))
        · exact Or.inl hbE) hUs hEs hadd hsub
  erw [h₃]
  exact ⟨_, exec_skip I _⟩

omit [Inhabited K] in
private theorem el6_map {α β : Type} {o : Option α} (f : α → β) (h : ∃ a, o = some a) :
    ∃ b, o.map f = some b := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f a, rfl⟩

/-- **One level of the upward pass succeeds** under the standard model with every value in range,
the exact floor conversion and an exact literal $2$, if kernel `mm` is a routine on pairs, with the
hypotheses of `NLAlib.holds_of_exec_eighUpLevel`. No printed source.
Proof: as `NLAlib.holds_of_exec_eighUpLevel`, each operation by its success clause: the binders
(`htn`), the kernel calls (`NLAlib.Computation.IsMatMulKernel.kcallStore_eq`, pilot; the output
block of depth $d$ does not overlap the inputs of depth $d + 1$ and the bases), the copies, sums and
differences (`bin_ok`). M, about 80 lines. -/
theorem exists_exec_eighUpLevel {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {two : Cell ℕ ℕ} {st : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (htwo : two.buf ∉ H.handles)
    (htwov : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1)) :
    ∃ st', exec I (eighUpLevel p mm (.const n) (.const d) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
      two).run st = some st' := by
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have hltH : ∀ b ∈ H.handles, b < st.store.size := by
    simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv]
  have htH : st.store.size ∉ H.handles := fun hm => absurd (hltH _ hm) (lt_irrefl _)
  obtain ⟨z2, hz2, hdz2⟩ := hlit p 2 (by omega)
  have htwo' : st.store.read p two.buf two.idx.eval = some z2 := htwov.trans hz2
  have ltwo := Store.lt_size_of_read_eq_some htwo'
  have hadd : ∀ x z, ∃ v, I.sem.bin p .add x z = some v :=
    fun x z => hsem.bin_ok p .add x z trivial (fun h => nomatch h) trivial
  have hsub : ∀ x z, ∃ v, I.sem.bin p .sub x z = some v :=
    fun x z => hsem.bin_ok p .sub x z trivial (fun h => nomatch h) trivial
  set M := eighTapeMachine I p mmR qrR with hM
  set t := st.store.size with ht
  change ∃ st', exec I (.seq (.alloc p _ _) .skip) st = some st'
  rw [exec_seq_skip, exec_alloc]
  refine el6_map _ ?_
  change ∃ s₁, exec I (.seq (.instr _) (.seq (.instr _) (.seq (.loop _ _) .skip))) _ = some s₁
  have hP : ∀ {q : P} {b i : ℕ}, b < t →
      Store.read (st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)) q b i =
        st.store.read q b i := fun hb => Store.read_push_of_lt hb
  have hPs : (Store.shape (st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)))[t]? =
      some (p, 2) := Store.getElem?_shape_push_size _ _ _
  have hxR : Store.read (st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)) p H.Lv
      (2 * IExp.const d : IExp ℕ).eval = some (eighLevelParams M R₀ ε ℓ₀ d).1 :=
    (hP (hltH _ (by simp [EighArenas.handles]))).trans hlev.2.2.1
  obtain ⟨v0, hv0⟩ := hsem.bin_ok p .div (eighLevelParams M R₀ ε ℓ₀ d).1 z2 trivial
    (fun _ => by rw [hdz2]; norm_num) trivial
  obtain ⟨wa, hwa⟩ := Store.exists_write_eq_some_of_getElem?_shape (p := p) (b := t) (i := 0) v0
    hPs (by norm_num)
  obtain ⟨v1, hv1, -⟩ := hsem.neg p v0
  obtain ⟨wb, hwb⟩ := Store.exists_write_eq_some_of_getElem?_shape (p := p) (b := t) (i := 1) v1
    ((Store.shape_of_write_eq_some hwa).symm ▸ hPs) (by norm_num)
  rw [exec_seq_instr_bin I (x := ⟨H.Lv, 2 * IExp.const d⟩) (y := two) hxR
    ((hP ltwo).trans htwo') hv0 hwa]
  rw [exec_seq_instr_un I (x := ⟨t, 0⟩) (Store.read_of_write_eq_some hwa) hv1 hwb]
  rw [exec_seq_skip]
  have hrd₀ : ∀ q b i, b < t → wb.read q b i = st.store.read q b i := fun q b i hb => by
    rw [Store.read_of_write_eq_some_of_ne hwb (Or.inl (Nat.ne_of_lt hb)),
      Store.read_of_write_eq_some_of_ne hwa (Or.inl (Nat.ne_of_lt hb)), hP hb]
  have ht0 : wb.read p t 0 = some (M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2)) := by
    rw [Store.read_of_write_eq_some_of_ne hwb (Or.inr (by decide)),
      Store.read_of_write_eq_some hwa]
    change some v0 = some ((I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1
      ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)
    rw [hz2, Option.getD_some, hv0, Option.getD_some]
  have ht1 : wb.read p t 1 = some (M.neg (M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2))) := by
    rw [Store.read_of_write_eq_some hwb]
    change some v1 = some ((I.sem.un p .neg ((I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1
      ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)).getD default)
    rw [hz2, Option.getD_some, hv0, Option.getD_some, hv1, Option.getD_some]
  have hshw : ∀ {b}, b < t → wb.shape[b]? = st.store.shape[b]? := fun hb => by
    rw [Store.shape_of_write_eq_some hwb, Store.shape_of_write_eq_some hwa,
      Store.getElem?_shape_push_of_lt _ hb]
  have hUs : wb.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)) := (hshw (hsz hUa)).trans hUa
  have hEs : wb.shape[H.Ea]? = some (p, n * (D + 1)) := (hshw (hsz hEa)).trans hEa
  obtain ⟨T1, T2, -⟩ := el5_transfer (H := H) (s := st.store) (s' := wb) (p := p) (M := M)
    (n := n) (F := F) (ℓ₀ := ℓ₀) (D := D) (d := d) (R₀ := R₀) (β := β)
    (root := ⟨n, A, R₀, ε, ℓ₀⟩) (sem := I.sem) fun q b i hb => hrd₀ q b i (hltH b hb)
  obtain ⟨-, -, T3'⟩ := el5_transfer (H := H) (s := st.store) (s' := wb) (p := p) (M := M)
    (n := n) (F := F) (ℓ₀ := ℓ₀) (D := D) (d := d + 1) (R₀ := R₀) (β := β)
    (root := ⟨n, A, R₀, ε, ℓ₀⟩) (sem := I.sem) fun q b i hb => hrd₀ q b i (hltH b hb)
  refine ⟨_, (exists_exec_loop_eq_some_of_forall (I := I) (n := .const n)
    (fun lo (s : St P K C) => s.store.shape = wb.shape ∧ s.pos = st.pos ∧
      (∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) → lo' < lo →
          (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
            2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
          (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
        s.store.read q b i = wb.read q b i) ∧
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
        eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) → lo' < lo →
        pairLayout.Holds s.store p H.Ua (2 * (n * n) * d + 2 * n * lo')
            (eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).1 ∧
          ∀ i : Fin y.k, s.store.read p H.Ea (n * d + lo' + i) = some
            ((eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).2 i))
    ?_ ?_).choose_spec.1⟩
  · exact ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · rintro lo hlo s ⟨hsh, hps, hfr, hdone⟩
    simp only [IExp.eval_const] at hlo
    obtain ⟨s', hs'⟩ := el6_step_ex hmm p n ℓ₀ F d D hd H t (s₀ := { st with store := wb })
      (s₁ := s) hlo hnd htH ht0 ht1 (T1 hlev) (T2 hrec) (T3' hout) hfr (hsh ▸ hUs) (hsh ▸ hEs)
      hadd hsub
    exact ⟨s', hs', el5_step hmm p n ℓ₀ F d D hd H t (s₀ := { st with store := wb }) hlo hnd
      htH ht0 ht1 (T1 hlev) (T2 hrec) (T3' hout) hsh hps hfr hdone hs'⟩

/-! ### The program -/

/-! #### Helpers of `NLAlib.holds_of_exec_eighProg` -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: a cell of the arenas lies at one depth only. -/
private theorem ep1_lc_eq {H : EighArenas} (hnd : H.handles.Nodup) {n d e b i : ℕ}
    (h1 : H.LevelCell n d b i) (h2 : H.LevelCell n e b i) : d = e := by
  have hm : ∀ m x y : ℕ, m * x ≤ i → i < m * (x + 1) → m * y ≤ i → i < m * (y + 1) → x = y := by
    intro m x y h1 h2 h3 h4
    by_contra hxy
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · have := Nat.mul_le_mul_left m (show x + 1 ≤ y by omega); omega
    · have := Nat.mul_le_mul_left m (show y + 1 ≤ x by omega); omega
  simp only [EighArenas.handles, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨_, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _⟩,
    ⟨_, _⟩, _, -⟩ := hnd
  unfold EighArenas.LevelCell at h1 h2
  rcases h1 with ⟨hb1, a1, a2⟩ | ⟨hb1, a1, a2⟩ | ⟨hb1, a1⟩ <;>
    rcases h2 with ⟨hb2, c1, c2⟩ | ⟨hb2, c1, c2⟩ | ⟨hb2, c1⟩
  · exact hm _ _ _ a1 a2 c1 c2
  · exfalso
    rcases hb1 with h | h | h <;> rcases hb2 with h' | h' | h' | h' <;>
      exact absurd (h.symm.trans h') ‹_›
  · exfalso
    rcases hb1 with h | h | h <;> exact absurd (h.symm.trans hb2) ‹_›
  · exfalso
    rcases hb2 with h' | h' | h' <;> rcases hb1 with h | h | h | h <;>
      first | exact absurd (h.symm.trans h') ‹_› | exact absurd (h'.symm.trans h) ‹_›
  · exact hm _ _ _ a1 a2 c1 c2
  · exfalso
    rcases hb1 with h | h | h | h <;> exact absurd (h.symm.trans hb2) ‹_›
  · exfalso
    rcases hb2 with h | h | h <;> exact absurd (h.symm.trans hb1) ‹_›
  · exfalso
    rcases hb2 with h | h | h | h <;> exact absurd (h.symm.trans hb1) ‹_›
  · omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: a block of at most $k^2$ complex words at the slot of a node of size $k$ lies at its
depth. -/
private theorem ep1_blk {n d lo k i : ℕ} (hk : lo + k ≤ n)
    (h1 : 2 * (n * n) * d + 2 * n * lo ≤ i) (h2 : i < 2 * (n * n) * d + 2 * n * lo + 2 * (k * k)) :
    2 * (n * n) * d ≤ i ∧ i < 2 * (n * n) * (d + 1) := by
  have e1 : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have e2 : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  constructor <;> nlinarith

omit [AddMonoid C] [Inhabited K] in
/-- EP1: the nodes of depth $d$ transfer to a store that reads the same on the node, size and
window cells of depth $d$. -/
private theorem ep1_lev_tr {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ d : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hn : 1 ≤ n)
    (hs : ∀ q b i, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → H.LevelCell n d b i →
      s'.read q b i = s.read q b i)
    (h : H.LevelHolds sem s p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.LevelHolds sem s' p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  have e4 : n * (d + 1) = n * d + n := by ring
  have hSz : ∀ lo k, lo < n → ReadsIdx sem s p H.Sz (n * d + lo) k →
      ReadsIdx sem s' p H.Sz (n * d + lo) k := fun lo k hlo hr =>
    el1_readsIdx_congr (hs p _ _ (Or.inr (Or.inl rfl))
      (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by omega⟩))) hr
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun a lo y ha hl => ?_, fun lo hlo hno => hSz lo 0 hlo (h2 lo hlo hno), ?_, ?_⟩
  · obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn hl
    obtain ⟨r1, r2⟩ := h1 a lo y ha hl
    exact ⟨hSz lo _ (by omega) r1, el1_holds_keep r2 fun i hi1 hi2 =>
      hs p _ _ (Or.inl rfl) (Or.inl ⟨Or.inl rfl, ep1_blk hkn hi1 hi2⟩)⟩
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))]; exact h3
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩))]; exact h4

omit [AddMonoid C] [Inhabited K] in
/-- EP1: the records of depth $d$ transfer to a store that reads the same on the output, basis,
eigenvalue, kind and split cells of depth $d$. -/
private theorem ep1_rec_tr {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ d : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hn : 1 ≤ n)
    (hs : ∀ q b i, (b = H.Ua ∨ b = H.Qa ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) →
      H.LevelCell n d b i → s'.read q b i = s.read q b i)
    (h : H.RecordHolds sem s p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.RecordHolds sem s' p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  have e4 : n * (d + 1) = n * d + n := by ring
  intro a lo y ha hl hk
  obtain ⟨-, hkn⟩ := eighLoc_bounds hn hl
  have hR : ∀ {b} k, (b = H.Kd ∨ b = H.Kp) → ReadsIdx sem s p b (n * d + lo) k →
      ReadsIdx sem s' p b (n * d + lo) k := fun k hb hr =>
    el1_readsIdx_congr (hs p _ _ (by rcases hb with h | h <;> simp [h])
      (Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩))) hr
  have hblk : ∀ {b} {l m : ℕ} {Y : Matrix (Fin l) (Fin m) (K × K)} (off : ℕ),
      (b = H.Ua ∨ b = H.Qa) → off + 2 * (l * m) ≤ 2 * (y.k * y.k) →
      pairLayout.Holds s p b (2 * (n * n) * d + 2 * n * lo + off) Y →
      pairLayout.Holds s' p b (2 * (n * n) * d + 2 * n * lo + off) Y :=
    fun off hb hle hY => el1_holds_keep hY fun i hi1 hi2 =>
      hs p _ _ (by rcases hb with h | h <;> simp [h])
        (Or.inl ⟨by rcases hb with h | h <;> simp [h], ep1_blk hkn (by omega) (by omega)⟩)
  have this := h a lo y ha hl hk
  revert this
  cases eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    rintro ⟨h1, h2, h3⟩
    refine ⟨hR 1 (Or.inl rfl) h1, ?_, fun i => (hs p _ _ (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inr (Or.inl ⟨Or.inl rfl, by omega, by have := i.isLt; omega⟩))).trans (h3 i)⟩
    simpa using hblk (Y := U) 0 (Or.inl rfl) (by omega) (by simpa using h2)
  | shift b A' σ => exact hR _ (Or.inl rfl)
  | split kp hkp Qp Qm Ap Am σ =>
    rintro ⟨h1, h2, h3, h4⟩
    have e5 : y.k * kp + y.k * (y.k - kp) = y.k * y.k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hkp]
    have e6 : y.k * kp ≤ y.k * y.k := Nat.mul_le_mul_left _ hkp
    refine ⟨hR 4 (Or.inl rfl) h1, hR kp (Or.inr rfl) h2, ?_, hblk (Y := Qm) _ (Or.inr rfl)
      (by omega) h4⟩
    simpa using hblk (Y := Qp) 0 (Or.inr rfl) (by omega) (by simpa using h3)

omit [AddMonoid C] [Inhabited K] in
/-- EP1: the outputs of depth $d$ transfer to a store that reads the same on the output and
eigenvalue cells of depth $d$. -/
private theorem ep1_out_tr {H : EighArenas} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ D d : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hn : 1 ≤ n)
    (hs : ∀ q b i, (b = H.Ua ∨ b = H.Ea) → H.LevelCell n d b i → s'.read q b i = s.read q b i)
    (h : H.OutHolds s p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.OutHolds s' p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  have e4 : n * (d + 1) = n * d + n := by ring
  intro a lo y ha hl
  obtain ⟨-, hkn⟩ := eighLoc_bounds hn hl
  obtain ⟨h1, h2⟩ := h a lo y ha hl
  exact ⟨el1_holds_keep h1 fun i hi1 hi2 => hs p _ _ (Or.inl rfl)
      (Or.inl ⟨Or.inr (Or.inl rfl), ep1_blk hkn hi1 hi2⟩),
    fun i => (hs p _ _ (Or.inr rfl) (Or.inr (Or.inl ⟨Or.inl rfl, by omega,
      by have := i.isLt; omega⟩))).trans (h2 i)⟩


omit [Inhabited K] in
/-- EP1: the run of an allocation, inverted. -/
private theorem ep1_alloc {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st st' : St P K C}
    (h : exec I (.alloc p len body) st = some st') :
    ∃ (S st₂ : St P K C), S.store = st.store.push (p, Array.replicate len.eval none) ∧
      S.store.shape[st.store.size]? = some (p, len.eval) ∧
      S.pos = st.pos ∧ exec I (body st.store.size) S = some st₂ ∧
      st'.store = Array.pop st₂.store := by
  rw [exec_alloc] at h
  obtain ⟨st₂, h2, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨_, st₂, ?_, ?_, ?_, h2, rfl⟩
  · rfl
  · exact Store.getElem?_shape_push_size _ _ _
  · rfl

omit [Inhabited K] in
/-- EP1: a literal, then the rest, inverted. -/
private theorem ep1_inv_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.lit p dst q)) t) s = some s₂) :
    ∃ v W σ, I.sem.lit p q = some v ∧ s.store.write p dst.buf dst.idx.eval v = some W ∧
      σ.store = W ∧ σ.pos = s.pos ∧ exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨v, s', _, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: an index literal, then the rest, inverted. -/
private theorem ep1_inv_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.litIdx p dst e)) t) s = some s₂) :
    ∃ v W σ, I.sem.lit p (e.eval : ℚ) = some v ∧ s.store.write p dst.buf dst.idx.eval v = some W ∧
      σ.store = W ∧ σ.pos = s.pos ∧ exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨v, s', _, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: a binary operation, then the rest, inverted. -/
private theorem ep1_inv_bin {p : P} {op : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.bin p op dst x y)) t) s = some s₂) :
    ∃ a c v W σ, s.store.read p x.buf x.idx.eval = some a ∧
      s.store.read p y.buf y.idx.eval = some c ∧ I.sem.bin p op a c = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some W ∧ σ.store = W ∧ σ.pos = s.pos ∧
      exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, c, hc, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨a, c, v, s', _, ha, hc, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: a unary operation, then the rest, inverted. -/
private theorem ep1_inv_un {p : P} {op : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.un p op dst x)) t) s = some s₂) :
    ∃ a v W σ, s.store.read p x.buf x.idx.eval = some a ∧ I.sem.un p op a = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some W ∧ σ.store = W ∧ σ.pos = s.pos ∧
      exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨a, v, s', _, ha, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: a copy, then the rest, inverted. -/
private theorem ep1_inv_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.copy p dst src)) t) s = some s₂) :
    ∃ v W σ, s.store.read p src.buf src.idx.eval = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some W ∧ σ.store = W ∧ σ.pos = s.pos ∧
      exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨v, s', _, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: a successful loop of index literals into the cells $w < m$ of one buffer leaves the
literal in each, every other cell, the shape and the positions unchanged. -/
private theorem ep1_litIdx_loop {p : P} {m e : IExp ℕ} {Y : ℕ} {st st' : St P K C}
    (h : exec I (.loop m fun w => (Builder.ins (ι := ι) (.litIdx p ⟨Y, .var w⟩ e)).run) st =
      some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ w < m.eval, st'.store.read p Y w = I.sem.lit p (e.eval : ℚ)) ∧
      ∀ q b i, (b ≠ Y ∨ m.eval ≤ i) → st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧ (∀ w' < w, s.store.read p Y w' = I.sem.lit p (e.eval : ℚ)) ∧
      ∀ q b i, (b ≠ Y ∨ w ≤ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  change exec I (.seq (.instr (.litIdx p ⟨Y, .var w⟩ e)) .skip) s₁ = some s₂ at hex
  obtain ⟨v, s', hv, hw', hex⟩ := el1_inv_litIdx hex
  rw [exec_skip, Option.some_inj] at hex
  subst hex
  simp only [IExp.eval_var] at hw'
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun w' hw => ?_, fun q b i hb => ?_⟩
  · change s'.read p Y w' = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega)), hrd w' h]
    · rw [Store.read_of_write_eq_some hw', hv]
  · change s'.read q b i = _
    rw [Store.read_of_write_eq_some_of_ne hw' ?_, hfr q b i (hb.imp_right fun h => by omega)]
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

omit [Inhabited K] in
/-- EP1: a successful loop of copies `Y[w] ← X[w]`, $w < m$, between distinct buffers. -/
private theorem ep1_copy_loop {p : P} {m : IExp ℕ} {X Y : ℕ} {st st' : St P K C} (hXY : X ≠ Y)
    (h : exec I (.loop m fun w => (Builder.ins (ι := ι)
      (.copy p ⟨Y, .var w⟩ ⟨X, .var w⟩)).run) st = some st') :
    st'.store.shape = st.store.shape ∧
      (∀ w < m.eval, st'.store.read p Y w = st.store.read p X w) ∧
      ∀ q b i, (b ≠ Y ∨ m.eval ≤ i) → st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      (∀ w' < w, s.store.read p Y w' = st.store.read p X w') ∧
      ∀ q b i, (b ≠ Y ∨ w ≤ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hrd, hfr⟩ hex
  change exec I (.seq (.instr (.copy p ⟨Y, .var w⟩ ⟨X, .var w⟩)) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  simp only [IExp.eval_var] at hw' hv
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, fun w' hw => ?_, fun q b i hb => ?_⟩
  · change s'.read p Y w' = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega)), hrd w' h]
    · rw [Store.read_of_write_eq_some hw', ← hv, hfr _ _ _ (Or.inl hXY)]
  · change s'.read q b i = _
    rw [Store.read_of_write_eq_some_of_ne hw' ?_, hfr q b i (hb.imp_right fun h => by omega)]
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

set_option maxHeartbeats 8000000 in
-- The walk goes through every statement of the level, the node step included.
omit [Inhabited K] in
/-- EP1: a level of the downward pass at an index variable runs as at the constant of its
value. -/
private theorem ep1_down_congr (p : P) (mm qr : ι)
    (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c : ℕ) (st : St P K C) :
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par Lv Su Sg Ma
      Ua Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st := by
  have hE : el1_Equiv I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv
      Su Sg Ma Ua Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
      (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) := by
    unfold eighDownLevel
    repeat' first
      | rfl
      | exact el1E_pure
      | apply el1E_ins
      | apply el1E_kcall
      | apply el1E_forRange
      | apply el1E_bindIdx
      | apply el1E_ite
      | apply el1E_named
      | apply el1E_scope
      | apply el1E_allocBind
      | apply el1E_bind
      | intro _
  exact hE (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

omit [Inhabited K] in
/-- EP1: the spent level at an index expression runs as at the constant of its value. -/
private theorem ep1_bottom_congr (p : P) (n D : ℕ) (De : IExp ℕ) (hD : De.eval = D)
    (Ua Ea Sz : ℕ) (st : St P K C) :
    exec I (eighBottomLevel (ι := ι) p (.const n) De Ua Ea Sz).run st =
      exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) Ua Ea Sz).run st := by
  subst hD
  have hE : el1_Equiv I (eighBottomLevel (ι := ι) p (.const n) De Ua Ea Sz)
      (eighBottomLevel (ι := ι) p (.const n) (.const De.eval) Ua Ea Sz) := by
    unfold eighBottomLevel
    repeat' first
      | rfl
      | exact el1E_pure
      | apply el1E_ins
      | apply el1E_kcall
      | apply el1E_forRange
      | apply el1E_bindIdx
      | apply el1E_ite
      | apply el1E_named
      | apply el1E_scope
      | apply el1E_allocBind
      | apply el1E_bind
      | intro _
  exact hE (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

set_option maxHeartbeats 1600000 in
-- The walk goes through every statement of the level.
omit [Inhabited K] in
/-- EP1: a level of the upward pass at an index expression runs as at the constant of its
value. -/
private theorem ep1_up_congr (p : P) (mm : ι) (n d : ℕ) (de : IExp ℕ) (hd : de.eval = d)
    (Lv Ua Qa Ea Sz Kd Kp c : ℕ) (st : St P K C) :
    exec I (eighUpLevel p mm (.const n) de Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run st =
      exec I (eighUpLevel p mm (.const n) (.const d) Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run st := by
  subst hd
  have hE : el1_Equiv I (eighUpLevel p mm (.const n) de Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩)
      (eighUpLevel p mm (.const n) (.const de.eval) Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩) := by
    unfold eighUpLevel
    repeat' first
      | rfl
      | exact el1E_pure
      | apply el1E_ins
      | apply el1E_kcall
      | apply el1E_forRange
      | apply el1E_bindIdx
      | apply el1E_ite
      | apply el1E_named
      | apply el1E_scope
      | apply el1E_allocBind
      | apply el1E_bind
      | intro _
  exact hE (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: a cell of a depth lies in one of the arenas. -/
private theorem ep1_lc_mem {H : EighArenas} {n e b i : ℕ} (h : H.LevelCell n e b i) :
    b ∈ H.handles := by
  unfold EighArenas.LevelCell at h
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ⟨h | h | h, -⟩ | ⟨h | h | h | h, -⟩ | ⟨h, -⟩ <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the node, size and window arenas are arenas. -/
private theorem ep1_mem3 {H : EighArenas} {b : ℕ} (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) :
    b ∈ H.handles := by
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the record arenas are arenas. -/
private theorem ep1_mem5 {H : EighArenas} {b : ℕ}
    (h : b = H.Ua ∨ b = H.Qa ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) : b ∈ H.handles := by
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h | h <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the node, size and window arenas are not record arenas. -/
private theorem ep1_disj {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv)
    (h' : b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) : False := by
  rcases h with rfl | rfl | rfl <;> rcases h' with h' | h' | h' | h' | h' <;>
    simp [EighArenas.handles, h'] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the node, size and window arenas are not the output or eigenvalue arenas. -/
private theorem ep1_disj' {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) (h' : b = H.Ua ∨ b = H.Ea) : False :=
  ep1_disj hnd h (by rcases h' with h' | h' <;> simp [h'])

set_option maxHeartbeats 1600000 in
-- The invariant of the downward pass carries five facts through every level.
/-- EP1: **the downward pass**: from the initialisation (the root at depth $0$, every size cell
below it $0$, the constants and the stored $R_0$, $\beta$), the loop of
`NLAlib.eighDownLevel` over the depths $d \le \ell_0$ ends with the nodes of depth $\ell_0 + 1$ and,
for every lower depth, its nodes and records (the precise frame of
`ep2_holds_of_exec_eighDownLevel` keeps them); every cell outside the arenas and the sample
buffers is kept. -/
private theorem ep1_down_pass {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F : ℕ) (hn1 : 1 ≤ n) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {σ0 σd : St P K C}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hH : ∀ s : Store P K, s.shape = σ0.store.shape → H.Shaped s p n (ℓ₀ + 1))
    (hpos : σ0.pos .uniform = 0 ∧ σ0.pos .gaussian = 0)
    (hlev : H.LevelHolds I.sem σ0.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ 0)
    (hz : ∀ e lo, 0 < e → e ≤ ℓ₀ + 1 → lo < n →
      ReadsIdx I.sem σ0.store p H.Sz (n * e + lo) 0)
    (hpar : σ0.store.read p par 0 = some R₀ ∧ σ0.store.read p par 2 = some β)
    (hc : σ0.store.read p c 0 = I.sem.lit p 1 ∧
      σ0.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      σ0.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      σ0.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      σ0.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (.loop (.const ℓ₀ + 1) fun d => (eighDownLevel p mm qr (.const n) (.const ℓ₀)
      (.const F) (.var d) par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩
      ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run) σ0 = some σd) :
    σd.store.shape = σ0.store.shape ∧
      H.LevelHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1) ∧
      (∀ e < ℓ₀ + 1, H.LevelHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
          ⟨n, A₀, R₀, ε, ℓ₀⟩ e ∧
        H.RecordHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F R₀ β
          ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      ∀ q b i, b ∉ H.handles → b ≠ Su → b ≠ Sg → σd.store.read q b i = σ0.store.read q b i := by
  set M := eighTapeMachine I p mmR qrR with hM
  have hnd : H.handles.Nodup := (List.nodup_append.mp hbufs).1
  have hdis := (List.nodup_append.mp hbufs).2.2
  have hparH : par ∉ H.handles := fun hm => hdis par hm par (by simp) rfl
  have hcH : c ∉ H.handles := fun hm => hdis c hm c (by simp) rfl
  have hSu : Su ∉ H.handles := fun hm => hdis Su hm Su (by simp) rfl
  have hSg : Sg ∉ H.handles := fun hm => hdis Sg hm Sg (by simp) rfl
  have h4 := (List.nodup_append.mp hbufs).2.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h4
  obtain ⟨⟨hparSu, hparSg, -⟩, ⟨-, hSuc⟩, hSgc, -⟩ := h4
  have hR := forall_of_exec_loop_eq_some I (st := σ0) (fun d (s : St P K C) =>
      s.store.shape = σ0.store.shape ∧ s.pos .uniform = n * d ∧
      s.pos .gaussian = 4 * (n * n) * d ∧
      H.LevelHolds I.sem s.store p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ d ∧
      (∀ e < d, H.LevelHolds I.sem s.store p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e ∧
        H.RecordHolds I.sem s.store p M n F R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ e lo, d < e → e ≤ ℓ₀ + 1 → lo < n → ReadsIdx I.sem s.store p H.Sz (n * e + lo) 0) ∧
      (∀ q b i, b ∉ H.handles → b ≠ Su → b ≠ Sg → s.store.read q b i = σ0.store.read q b i))
    ⟨rfl, by rw [hpos.1, Nat.mul_zero], by rw [hpos.2, Nat.mul_zero], hlev,
      fun e he => absurd he (Nat.not_lt_zero _), hz, fun _ _ _ _ _ _ => rfl⟩ ?_ h
  · obtain ⟨hsh, -, -, hL, hlow, -, hfr⟩ := hR
    exact ⟨hsh, hL, hlow, hfr⟩
  intro d hd s₁ s₂ ⟨hsh1, hpu1, hpg1, hL1, hlow1, hz1, hfr1⟩ hex
  change d < ℓ₀ + 1 at hd
  have hex' := (ep1_down_congr p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
    H.Kp c s₁).symm.trans hex
  have hcs : ∀ j, s₁.store.read p c j = σ0.store.read p c j := fun j =>
    hfr1 p c j hcH (Ne.symm hSuc) (Ne.symm hSgc)
  obtain ⟨hL2, hR2, hfr2, hsh2, hpu2, hpg2⟩ := ep2_holds_of_exec_eighDownLevel hmm hqr p hflag hcmp
    n ℓ₀ F d (ℓ₀ + 1) hd hlit htn H (par := par) (Su := Su) (Sg := Sg) (c := c)
    (hH _ hsh1) hbufs hL1 (fun lo hlo => hz1 (d + 1) lo (by omega) (by omega) hlo)
    ⟨hpu1, hpg1⟩
    ⟨(hfr1 p par 0 hparH hparSu hparSg).trans hpar.1,
      (hfr1 p par 2 hparH hparSu hparSg).trans hpar.2⟩
    ⟨(hcs 0).trans hc.1, (hcs 1).trans hc.2.1, (hcs 2).trans hc.2.2.1,
      (hcs 3).trans hc.2.2.2.1, (hcs 4).trans hc.2.2.2.2⟩ hex'
  refine ⟨hsh2.trans hsh1, by rw [hpu2, hpu1]; ring, by rw [hpg2, hpg1]; ring, hL2,
    fun e he => ?_, fun e lo he1 he2 hlo => ?_, fun q b i hb h1 h2 => ?_⟩
  · have hL : H.LevelHolds I.sem s₁.store p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
      · exact (hlow1 e he).1
      · exact hL1
    refine ⟨ep1_lev_tr hn1 (fun q b i hb hlc => hfr2 q b i
      (fun e => hSu (e ▸ ep1_mem3 hb)) (fun e => hSg (e ▸ ep1_mem3 hb))
      (fun h => ep1_disj hnd hb h.1)
      (fun h => by have := ep1_lc_eq hnd hlc h; omega)) hL, ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he' | rfl
    · exact ep1_rec_tr hn1 (fun q b i hb hlc => hfr2 q b i
        (fun e => hSu (e ▸ ep1_mem5 hb)) (fun e => hSg (e ▸ ep1_mem5 hb))
        (fun h => by have := ep1_lc_eq hnd hlc h.2; omega)
        (fun h => by have := ep1_lc_eq hnd hlc h; omega)) (hlow1 e he').2
    · exact hR2
  · have hlc : H.LevelCell n e H.Sz (n * e + lo) :=
      Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by rw [Nat.mul_succ]; omega⟩)
    have hSzm : H.Sz = H.Ma ∨ H.Sz = H.Sz ∨ H.Sz = H.Lv := Or.inr (Or.inl rfl)
    exact el1_readsIdx_congr (hfr2 p H.Sz (n * e + lo)
      (fun e => hSu (e ▸ ep1_mem3 hSzm)) (fun e => hSg (e ▸ ep1_mem3 hSzm))
      (fun h => ep1_disj hnd hSzm h.1)
      (fun h => by have := ep1_lc_eq hnd hlc h; omega))
      (hz1 e lo (by omega) he2 hlo)
  · refine (hfr2 q b i h1 h2 (fun h => hb ?_) (fun h => hb (ep1_lc_mem h))).trans
      (hfr1 q b i hb h1 h2)
    obtain ⟨h', -⟩ := h
    exact ep1_mem5 (by rcases h' with h | h | h | h | h <;> simp [h])

set_option maxHeartbeats 1600000 in
-- The invariant of the upward pass carries three facts through every level.
/-- EP1: **the spent level and the upward pass**: from the nodes of depth $\ell_0 + 1$ and the
nodes and records of every lower depth, `NLAlib.eighBottomLevel` and the loop of
`NLAlib.eighUpLevel` over the depths $\ell_0, \ldots, 0$ end with the outputs of depth $0$; every
cell outside the output and eigenvalue arenas is kept. -/
private theorem ep1_up_pass {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {dec : P → K → ℝ} (p : P) (n ℓ₀ F : ℕ) (hn1 : 1 ≤ n)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {c : ℕ} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {σd σb σu : St P K C}
    (hnd : H.handles.Nodup)
    (hH : ∀ s : Store P K, s.shape = σd.store.shape → H.Shaped s p n (ℓ₀ + 1))
    (htwo : c ∉ H.handles) (htwov : σd.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlevD : H.LevelHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1))
    (hlow : ∀ e < ℓ₀ + 1, H.LevelHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀
        β ⟨n, A₀, R₀, ε, ℓ₀⟩ e ∧
      H.RecordHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e)
    (hbot : exec I (eighBottomLevel (ι := ι) p (.const n) (.const (ℓ₀ + 1)) H.Ua H.Ea H.Sz).run
      σd = some σb)
    (h : exec I (.loop (.const ℓ₀ + 1) fun j => (eighUpLevel p mm (.const n) (.const ℓ₀ - .var j)
      H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 1⟩).run) σb = some σu) :
    σu.store.shape = σd.store.shape ∧
      H.OutHolds σu.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ 0 ∧
      ∀ q b i, b ≠ H.Ua → b ≠ H.Ea → σu.store.read q b i = σd.store.read q b i := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hOD, hfrB, hshB, -⟩ := holds_of_exec_eighBottomLevel p n ℓ₀ F (ℓ₀ + 1) hlit htn H
    (A := A₀) (ε := ε) (hH _ rfl) hlevD hbot
  have hR := forall_of_exec_loop_eq_some I (st := σb) (fun j (s : St P K C) =>
      s.store.shape = σd.store.shape ∧
      H.OutHolds s.store p M n F (ℓ₀ + 1) R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1 - j) ∧
      (∀ e < ℓ₀ + 1 - j, H.LevelHolds I.sem s.store p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e ∧
        H.RecordHolds I.sem s.store p M n F R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ q b i, b ≠ H.Ua → b ≠ H.Ea → s.store.read q b i = σd.store.read q b i))
    ⟨hshB, hOD, fun e he => ⟨ep1_lev_tr hn1 (fun q b i hb hlc => hfrB q b i
        (fun h => ep1_disj' hnd hb h.1)) (hlow e he).1,
      ep1_rec_tr hn1 (fun q b i hb hlc => hfrB q b i
        (fun h => by have := ep1_lc_eq hnd hlc h.2; omega)) (hlow e he).2⟩,
      fun q b i h1 h2 => hfrB q b i (fun h => h.1.elim h1 h2)⟩ ?_ h
  · obtain ⟨hsh, hO, -, hfr⟩ := hR
    change H.OutHolds σu.store p M n F (ℓ₀ + 1) R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1 - (ℓ₀ + 1)) at hO
    rw [Nat.sub_self] at hO
    exact ⟨hsh, hO, hfr⟩
  intro j hj s₁ s₂ ⟨hsh1, hO1, hlow1, hfr1⟩ hex
  change j < ℓ₀ + 1 at hj
  have hex' : exec I (eighUpLevel p mm (.const n) (.const (ℓ₀ - j)) H.Lv H.Ua H.Qa H.Ea H.Sz
      H.Kd H.Kp ⟨c, 1⟩).run s₁ = some s₂ := by
    rw [← ep1_up_congr p mm n (ℓ₀ - j) (.const ℓ₀ - .var j) rfl]
    exact hex
  have e1 : ℓ₀ - j + 1 = ℓ₀ + 1 - j := by omega
  have hOut : H.OutHolds s₁.store p M n F (ℓ₀ + 1) R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ - j + 1) := by
    rw [e1]; exact hO1
  obtain ⟨hO2, hfr2, hsh2, -⟩ := holds_of_exec_eighUpLevel hmm p n ℓ₀ F (ℓ₀ - j) (ℓ₀ + 1)
    (by omega) hlit htn H (two := ⟨c, 1⟩) (A := A₀) (hH _ hsh1) htwo
    ((hfr1 p c 1 (fun h => htwo (by rw [h]; simp [EighArenas.handles]))
      (fun h => htwo (by rw [h]; simp [EighArenas.handles]))).trans htwov)
    (hlow1 _ (by omega)).1 (hlow1 _ (by omega)).2 hOut hex'
  have e2 : ℓ₀ + 1 - (j + 1) = ℓ₀ - j := by omega
  refine ⟨hsh2.trans hsh1, by rw [e2]; exact hO2, fun e he => ?_,
    fun q b i h1 h2 => (hfr2 q b i (fun h => h.1.elim h1 h2)).trans
      (hfr1 q b i h1 h2)⟩
  rw [e2] at he
  exact ⟨ep1_lev_tr hn1 (fun q b i hb hlc => hfr2 q b i
      (fun h => ep1_disj' hnd hb h.1)) (hlow1 e (by omega)).1,
    ep1_rec_tr hn1 (fun q b i hb hlc => hfr2 q b i
      (fun h => by have := ep1_lc_eq hnd hlc h.2; omega)) (hlow1 e (by omega)).2⟩


omit [AddMonoid C] [Inhabited K] in
/-- EP1: a pushed store reads as before below its old size. -/
private theorem ep1_push {S S' : St P K C} {x : P × Array (Option K)}
    (h : S'.store = S.store.push x) {b : ℕ} (hb : b < S.store.size) :
    S'.store.shape[b]? = S.store.shape[b]? ∧ ∀ q i, S'.store.read q b i = S.store.read q b i := by
  rw [h]
  exact ⟨Store.getElem?_shape_push_of_lt _ hb, fun q i => Store.read_push_of_lt hb⟩

omit [AddMonoid C] [Inhabited K] in
/-- EP1: a popped store reads as before below its new size. -/
private theorem ep1_pop {s s' : Store P K} {m : ℕ} (he : s' = Array.pop s) (hs : s.size = m + 1) :
    s'.size = m ∧ ∀ q b i, b < m → s'.read q b i = s.read q b i := by
  subst he
  exact ⟨by simp [hs], fun q b i hb => Store.read_pop_of_lt (by omega)⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the handles of the program's buffers are distinct. -/
private theorem ep1_nodup {t par : ℕ} (hp : par < t) :
    ([t + 1, t + 2, t + 3, t + 4, t + 5, t + 6, t + 7, t + 8] ++
      [par, t + 9, t + 10, t]).Nodup := by
  simp
  omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the constants are not an arena. -/
private theorem ep1_notMem (t : ℕ) :
    t ∉ [t + 1, t + 2, t + 3, t + 4, t + 5, t + 6, t + 7, t + 8] := by
  simp

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the tree of `NLAlib.eighProg`, its eleven allocations and its body. -/
private theorem ep1_prog_eq (p : P) (mm qr : ι) (n ℓ₀ F A par U dv : ℕ) :
    (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run =
      .seq (.alloc p 5 fun c => .alloc p (2 * (.const n * .const n) * (.const ℓ₀ + 1 + 1)) fun Ma =>
        .alloc p (2 * (.const n * .const n) * (.const ℓ₀ + 1 + 1)) fun Ua =>
        .alloc p (2 * (.const n * .const n) * (.const ℓ₀ + 1)) fun Qa =>
        .alloc p (.const n * (.const ℓ₀ + 1 + 1)) fun Ea =>
        .alloc p (.const n * (.const ℓ₀ + 1 + 1) + 1) fun Sz =>
        .alloc p (.const n * (.const ℓ₀ + 1)) fun Kd =>
        .alloc p (.const n * (.const ℓ₀ + 1)) fun Kp =>
        .alloc p (2 * (.const ℓ₀ + 1 + 1)) fun Lv =>
        .alloc p (.const n) fun Su =>
        .alloc p (4 * (.const n * .const n)) fun Sg => (do
        ins (.lit p ⟨c, 0⟩ 1)
        ins (.litIdx p ⟨c, 1⟩ 2)
        ins (.bin p .div ⟨c, 2⟩ ⟨c, 0⟩ ⟨c, 1⟩)
        ins (.un p .neg ⟨c, 3⟩ ⟨c, 0⟩)
        ins (.un p .sqrt ⟨c, 4⟩ ⟨c, 2⟩)
        forRange (.const n * (.const ℓ₀ + 1 + 1) + 1) fun w => ins (.litIdx p ⟨Sz, .var w⟩ 0)
        ins (.litIdx p ⟨Sz, 0⟩ (.const n))
        zcopy p (.const n) (.const n) A 0 Ma 0
        ins (.copy p ⟨Lv, 0⟩ ⟨par, 0⟩)
        ins (.copy p ⟨Lv, 1⟩ ⟨par, 1⟩)
        forRange (.const ℓ₀ + 1) fun d =>
          eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv Su Sg Ma Ua Qa
            Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
        eighBottomLevel p (.const n) (.const ℓ₀ + 1) Ua Ea Sz
        forRange (.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩
        zcopy p (.const n) (.const n) Ua 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨Ea, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run) .skip := by
  rfl

set_option maxHeartbeats 4000000 in
-- The run unfolds the initialisation, the two passes and the copies out.
/-- EP1: **the body of `NLAlib.eighProg`** after its eleven allocations (the constants at `t`,
the arenas at `t + 1` to `t + 8`, the samples at `t + 9`, `t + 10`): a successful run ends with
the root's output of `NLAlib.eigh` in `U` and `dv`, with the store shape kept. -/
private theorem ep1_body {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F : ℕ) (hn1 : n > 0) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) {A par U dv t : ℕ} {st S s11 : St P K C}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} (hAt : A < t) (hpart : par < t)
    (hUt : U < t) (hdvt : dv < t) (hUdv : U ≠ dv) (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0)
    (hold : ∀ q b i, b < t → S.store.read q b i = st.store.read q b i) (hposS : S.pos = st.pos)
    (hsh1 : S.store.shape[t + 1]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)))
    (hsh2 : S.store.shape[t + 2]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)))
    (hsh3 : S.store.shape[t + 3]? = some (p, 2 * (n * n) * (ℓ₀ + 1)))
    (hsh4 : S.store.shape[t + 4]? = some (p, n * (ℓ₀ + 1 + 1)))
    (hsh5 : S.store.shape[t + 5]? = some (p, n * (ℓ₀ + 1 + 1) + 1))
    (hsh6 : S.store.shape[t + 6]? = some (p, n * (ℓ₀ + 1)))
    (hsh7 : S.store.shape[t + 7]? = some (p, n * (ℓ₀ + 1)))
    (hsh8 : S.store.shape[t + 8]? = some (p, 2 * (ℓ₀ + 1 + 1)))
    (h : exec I (do
        ins (.lit p ⟨t, 0⟩ 1)
        ins (.litIdx p ⟨t, 1⟩ 2)
        ins (.bin p .div ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        ins (.un p .neg ⟨t, 3⟩ ⟨t, 0⟩)
        ins (.un p .sqrt ⟨t, 4⟩ ⟨t, 2⟩)
        forRange (.const n * (.const ℓ₀ + 1 + 1) + 1) fun w => ins (.litIdx p ⟨t + 5, .var w⟩ 0)
        ins (.litIdx p ⟨t + 5, 0⟩ (.const n))
        zcopy p (.const n) (.const n) A 0 (t + 1) 0
        ins (.copy p ⟨t + 8, 0⟩ ⟨par, 0⟩)
        ins (.copy p ⟨t + 8, 1⟩ ⟨par, 1⟩)
        forRange (.const ℓ₀ + 1) fun d =>
          eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par (t + 8) (t + 9)
            (t + 10) (t + 1) (t + 2) (t + 3) (t + 4) (t + 5) (t + 6) (t + 7) ⟨t, 0⟩ ⟨t, 1⟩ ⟨t, 2⟩
            ⟨t, 3⟩ ⟨t, 4⟩
        eighBottomLevel p (.const n) (.const ℓ₀ + 1) (t + 2) (t + 4) (t + 5)
        forRange (.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') (t + 8) (t + 2) (t + 3) (t + 4)
            (t + 5) (t + 6) (t + 7) ⟨t, 1⟩
        zcopy p (.const n) (.const n) (t + 2) 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨t + 4, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run S = some s11) :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M n F R₀ β 0 0 ⟨n, A₀, R₀, ε, ℓ₀⟩)
    s11.store.shape = S.store.shape ∧ pairLayout.Holds s11.store p U 0 r.1 ∧
      ∀ i : Fin n, s11.store.read p dv i = some (r.2 i) := by
  intro M r
  -- the initialisation
  obtain ⟨v0, W1, T1, hv0, hw1, hT1, hq1, g12⟩ := ep1_inv_lit h
  clear h
  obtain ⟨v1, W2, T2, hv1, hw2, hT2, hq2, g13⟩ := ep1_inv_litIdx g12
  clear g12
  obtain ⟨a2, b2, v2, W3, T3, ha2, hb2', hv2, hw3, hT3, hq3, g14⟩ := ep1_inv_bin g13
  clear g13
  obtain ⟨a3, v3, W4, T4, ha3, hv3, hw4, hT4, hq4, g15⟩ := ep1_inv_un g14
  clear g14
  obtain ⟨a4, v4, W5, T5, ha4, hv4, hw5, hT5, hq5, g16⟩ := ep1_inv_un g15
  clear g15
  obtain ⟨σ6, h6, g17⟩ := el1_seq g16
  clear g16
  obtain ⟨v7, W7, T7, hv7, hw7, hT7, hq7, g18⟩ := ep1_inv_litIdx g17
  clear g17
  obtain ⟨σ8, h8, g19⟩ := el1_seq g18
  clear g18
  obtain ⟨v9, W9, T9, hv9, hw9, hT9, hq9, g20⟩ := ep1_inv_copy g19
  clear g19
  obtain ⟨v10, W10, T10, hv10, hw10, hT10, hq10, g21⟩ := ep1_inv_copy g20
  clear g20
  obtain ⟨σd, hdown, g22⟩ := el1_seq g21
  clear g21
  obtain ⟨σb, hbot, g23⟩ := el1_seq g22
  clear g22
  obtain ⟨σu, hup, g24⟩ := el1_seq g23
  clear g23
  obtain ⟨σz, hz, g25⟩ := el1_seq g24
  clear g24
  change exec I (.seq (.loop _ _) .skip) σz = some s11 at g25
  rw [exec_seq_skip] at g25
  -- the stores of the initialisation
  have hw1' : S.store.write p t 0 v0 = some W1 := hw1
  have hw2' : W1.write p t 1 v1 = some W2 := by rw [← hT1]; exact hw2
  have hw3' : W2.write p t 2 v2 = some W3 := by rw [← hT2]; exact hw3
  have hw4' : W3.write p t 3 v3 = some W4 := by rw [← hT3]; exact hw4
  have hw5' : W4.write p t 4 v4 = some W5 := by rw [← hT4]; exact hw5
  have hw7' : σ6.store.write p (t + 5) 0 v7 = some W7 := hw7
  have hw9' : σ8.store.write p (t + 8) 0 v9 = some W9 := hw9
  have hw10' : W9.write p (t + 8) 1 v10 = some W10 := by rw [← hT9]; exact hw10
  rw [hT9] at hv10
  rw [hT2] at ha2 hb2'
  rw [hT3] at ha3
  rw [hT4] at ha4
  have hv1' : I.sem.lit p ((2 : ℕ) : ℚ) = some v1 := hv1
  have hv7' : I.sem.lit p ((n : ℕ) : ℚ) = some v7 := hv7
  obtain ⟨sh6, ps6, rd6, fr6⟩ := ep1_litIdx_loop h6
  have sh6' : σ6.store.shape = W5.shape := by rw [sh6, hT5]
  have ps6' : σ6.pos = S.pos := by rw [ps6, hq5, hq4, hq3, hq2, hq1]
  have rd6' : ∀ w < n * (ℓ₀ + 1 + 1) + 1, σ6.store.read p (t + 5) w =
      I.sem.lit p ((0 : ℕ) : ℚ) := rd6
  have fr6' : ∀ q b i, (b ≠ t + 5 ∨ n * (ℓ₀ + 1 + 1) + 1 ≤ i) →
      σ6.store.read q b i = W5.read q b i := fun q b i h => (fr6 q b i h).trans (by rw [hT5])
  -- the old buffers before the copy of A
  have hr5 : ∀ q b i, b < t → W5.read q b i = st.store.read q b i := by
    intro q b i hb
    rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw3' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl (by omega)), hold q b i hb]
  have hr7 : ∀ q b i, b < t → W7.read q b i = st.store.read q b i := by
    intro q b i hb
    rw [Store.read_of_write_eq_some_of_ne hw7' (Or.inl (by omega)),
      fr6' q b i (Or.inl (by omega)), hr5 q b i hb]
  -- the copy of A into the node arena
  have hA7 : pairLayout.Holds W7 p A (0 : IExp ℕ).eval A₀ :=
    el1_holds_keep hA fun i _ _ => hr7 p A i hAt
  have hA7' : pairLayout.Holds T7.store p A (0 : IExp ℕ).eval A₀ := by rw [hT7]; exact hA7
  obtain ⟨hM8, fr8, sh8, ps8⟩ := holds_of_exec_zcopy (st := T7) p n n (X := A) (Y := t + 1)
    (xo := 0) (yo := 0) hA7' (el1_bd_ne (by omega)) ((exec_seq_skip I _ _).trans h8)
  have fr8' : ∀ q b i, b ≠ t + 1 → σ8.store.read q b i = W7.read q b i :=
    fun q b i hb => (fr8 q b i (el1_bd_ne hb)).trans (by rw [hT7])
  have sh8' : σ8.store.shape = W7.shape := by rw [sh8, hT7]
  have ps8' : σ8.pos = σ6.pos := by rw [ps8, hq7]
  have hr10 : ∀ q b i, b ≠ t + 1 → b ≠ t + 8 → W10.read q b i = W7.read q b i := by
    intro q b i h1 h2
    rw [Store.read_of_write_eq_some_of_ne hw10' (Or.inl h2),
      Store.read_of_write_eq_some_of_ne hw9' (Or.inl h2), fr8' q b i h1]
  have hold10 : ∀ q b i, b < t → W10.read q b i = st.store.read q b i := fun q b i hb =>
    (hr10 q b i (by omega) (by omega)).trans (hr7 q b i hb)
  have hv9' : v9 = R₀ := by
    have e1 : σ8.store.read p par 0 = some R₀ := by
      rw [fr8' p par 0 (by omega), hr7 p par 0 hpart, hpar.1]
    have e2 : σ8.store.read p par 0 = some v9 := hv9
    exact Option.some_inj.mp (e2.symm.trans e1)
  have hv10' : v10 = ε := by
    have e1 : W9.read p par 1 = some ε := by
      rw [Store.read_of_write_eq_some_of_ne hw9' (Or.inl (by omega)), fr8' p par 1 (by omega),
        hr7 p par 1 hpart, hpar.2.1]
    have e2 : W9.read p par 1 = some v10 := hv10
    exact Option.some_inj.mp (e2.symm.trans e1)
  rw [hv9'] at hw9'
  rw [hv10'] at hw10'
  -- the constants
  have ha2' : a2 = v0 := by
    have e1 : W2.read p t 0 = some v0 := by
      rw [Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw1']
    have e2 : W2.read p t 0 = some a2 := ha2
    exact Option.some_inj.mp (e2.symm.trans e1)
  have hb2'' : b2 = v1 := by
    have e2 : W2.read p t 1 = some b2 := hb2'
    exact Option.some_inj.mp (e2.symm.trans (Store.read_of_write_eq_some hw2'))
  have ha3' : a3 = v0 := by
    have e1 : W3.read p t 0 = some v0 := by
      rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw1']
    have e2 : W3.read p t 0 = some a3 := ha3
    exact Option.some_inj.mp (e2.symm.trans e1)
  have ha4' : a4 = v2 := by
    have e1 : W4.read p t 2 = some v2 := by
      rw [Store.read_of_write_eq_some_of_ne hw4' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw3']
    have e2 : W4.read p t 2 = some a4 := ha4
    exact Option.some_inj.mp (e2.symm.trans e1)
  rw [ha2', hb2''] at hv2
  rw [ha3'] at hv3
  rw [ha4'] at hv4
  have hc5 : W5.read p t 0 = some v0 ∧ W5.read p t 1 = some v1 ∧ W5.read p t 2 = some v2 ∧
      W5.read p t 3 = some v3 ∧ W5.read p t 4 = some v4 := by
    refine ⟨?_, ?_, ?_, ?_, Store.read_of_write_eq_some hw5'⟩
    · rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw4' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw1']
    · rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw4' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw2']
    · rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw4' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw3']
    · rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw4']
  have hc10 : ∀ j, W10.read p t j = W5.read p t j := fun j => by
    rw [hr10 p t j (by omega) (by omega),
      Store.read_of_write_eq_some_of_ne hw7' (Or.inl (by omega)),
      fr6' p t j (Or.inl (by omega))]
  have hcM : W10.read p t 0 = I.sem.lit p 1 ∧ W10.read p t 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      W10.read p t 2 = some (M.div M.one (M.ofNat 2)) ∧ W10.read p t 3 = some (M.neg M.one) ∧
      W10.read p t 4 = some (I.sem.sqrtHalf p) := by
    rw [hc10, hc10, hc10, hc10, hc10, hc5.1, hc5.2.1, hc5.2.2.1, hc5.2.2.2.1, hc5.2.2.2.2, hv0,
      hv1']
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · change some v2 = some ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)
      rw [hv0, hv1', Option.getD_some, Option.getD_some, hv2, Option.getD_some]
    · change some v3 = some ((I.sem.un p .neg ((I.sem.lit p 1).getD default)).getD default)
      rw [hv0, Option.getD_some, hv3, Option.getD_some]
    · unfold ScalarSem.sqrtHalf
      rw [hv0, hv1', Option.getD_some, Option.getD_some, hv2, Option.getD_some, hv4,
        Option.getD_some]
  -- the arenas and the stored state after the initialisation
  let H : EighArenas := ⟨t + 1, t + 2, t + 3, t + 4, t + 5, t + 6, t + 7, t + 8⟩
  have hHMa : H.Ma = t + 1 := rfl
  have hHUa : H.Ua = t + 2 := rfl
  have hHQa : H.Qa = t + 3 := rfl
  have hHEa : H.Ea = t + 4 := rfl
  have hHSz : H.Sz = t + 5 := rfl
  have hHKd : H.Kd = t + 6 := rfl
  have hHKp : H.Kp = t + 7 := rfl
  have hHLv : H.Lv = t + 8 := rfl
  have hbufs' : (H.handles ++ [par, t + 9, t + 10, t]).Nodup := ep1_nodup hpart
  have hnd : H.handles.Nodup := (List.nodup_append.mp hbufs').1
  have hshW : W10.shape = S.store.shape := by
    rw [Store.shape_of_write_eq_some hw10', Store.shape_of_write_eq_some hw9', sh8',
      Store.shape_of_write_eq_some hw7', sh6', Store.shape_of_write_eq_some hw5',
      Store.shape_of_write_eq_some hw4', Store.shape_of_write_eq_some hw3',
      Store.shape_of_write_eq_some hw2', Store.shape_of_write_eq_some hw1']
  have HS : ∀ s : Store P K, s.shape = S.store.shape → H.Shaped s p n (ℓ₀ + 1) := by
    intro s hs
    unfold EighArenas.Shaped
    rw [hs]
    exact ⟨hnd, hsh1, hsh2, hsh3, hsh4, hsh5, hsh6, hsh7, hsh8⟩
  have hSz10 : ∀ w, w ≠ 0 → w < n * (ℓ₀ + 1 + 1) + 1 →
      W10.read p (t + 5) w = I.sem.lit p ((0 : ℕ) : ℚ) := by
    intro w hw0 hw
    rw [hr10 p _ w (by omega) (by omega), Store.read_of_write_eq_some_of_ne hw7' (Or.inr hw0),
      rd6' w hw]
  have hSz0 : W10.read p (t + 5) 0 = I.sem.lit p ((n : ℕ) : ℚ) := by
    rw [hr10 p _ 0 (by omega) (by omega), Store.read_of_write_eq_some hw7', hv7']
  have hMa10 : pairLayout.Holds W10 p (t + 1) 0 A₀ := el1_holds_keep hM8 fun i _ _ => by
    rw [Store.read_of_write_eq_some_of_ne hw10' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw9' (Or.inl (by omega))]
  have hLv0 : W10.read p (t + 8) 0 = some R₀ := by
    rw [Store.read_of_write_eq_some_of_ne hw10' (Or.inr (by decide)),
      Store.read_of_write_eq_some hw9']
  have hLv1 : W10.read p (t + 8) 1 = some ε := Store.read_of_write_eq_some hw10'
  have hlev0 : H.LevelHolds I.sem W10 p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ 0 := by
    refine ⟨fun a lo y ha hl => ?_, fun lo hlo hno => ?_, hLv0, hLv1⟩
    · obtain rfl := List.eq_nil_of_length_eq_zero ha
      simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨el1_readsIdx hlit htn (k := n) (by omega)
        (show W10.read p (t + 5) (n * 0 + 0) = I.sem.lit p ((n : ℕ) : ℚ) by
          rw [Nat.mul_zero]; exact hSz0),
        show pairLayout.Holds W10 p (t + 1) (2 * (n * n) * 0 + 2 * n * 0) A₀ by
          rw [Nat.mul_zero, Nat.mul_zero]; exact hMa10⟩
    · have hlo0 : lo ≠ 0 := by
        rintro rfl
        exact hno [] ⟨n, A₀, R₀, ε, ℓ₀⟩ rfl rfl
      have : n ≤ n * (ℓ₀ + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
      exact el1_readsIdx hlit htn (k := 0) (by omega)
        (show W10.read p (t + 5) (n * 0 + lo) = I.sem.lit p ((0 : ℕ) : ℚ) by
          rw [Nat.mul_zero, Nat.zero_add]; exact hSz10 lo hlo0 (by omega))
  -- the downward pass
  have hT10' : T10.store.shape = S.store.shape := by rw [hT10]; exact hshW
  have hpos0 : T10.pos = st.pos := by
    rw [hq10, hq9, ps8', ps6', hposS]
  obtain ⟨hshD, hLD, hlowD, hfrD⟩ := ep1_down_pass hmm hqr p hflag hcmp n ℓ₀ F hn1 hlit htn H
    (par := par) (Su := t + 9) (Sg := t + 10) (c := t) (A₀ := A₀) (ε := ε) (σ0 := T10) hbufs'
    (fun s hs => HS s (hs.trans hT10')) (by rw [hpos0]; exact hpos) (by rw [hT10]; exact hlev0)
    (fun e lo he1 he2 hlo => by
      have h1 : n * e ≤ n * (ℓ₀ + 1) := Nat.mul_le_mul_left _ he2
      have h2 : n ≤ n * e := Nat.le_mul_of_pos_right _ he1
      have h3 : n * (ℓ₀ + 1 + 1) = n * (ℓ₀ + 1) + n := by ring
      rw [hT10]
      exact el1_readsIdx hlit htn (k := 0) (by omega) (hSz10 _ (by omega) (by omega)))
    (by rw [hT10]; exact ⟨(hold10 p par 0 hpart).trans hpar.1,
      (hold10 p par 2 hpart).trans hpar.2.2⟩)
    (by rw [hT10]; exact hcM) hdown
  -- the spent level and the upward pass
  have hbot' : exec I (eighBottomLevel (ι := ι) p (.const n) (.const (ℓ₀ + 1)) (t + 2) (t + 4)
      (t + 5)).run σd = some σb := by
    rw [← ep1_bottom_congr p n (ℓ₀ + 1) (IExp.const ℓ₀ + 1) rfl]
    exact (exec_seq_skip I _ _).trans hbot
  have htH : t ∉ H.handles := ep1_notMem t
  have hcD : σd.store.read p t 1 = I.sem.lit p ((2 : ℕ) : ℚ) := by
    rw [hfrD p t 1 htH (by omega) (by omega), hT10]; exact hcM.2.1
  obtain ⟨hshU, hO0, -⟩ := ep1_up_pass hmm p n ℓ₀ F hn1 hlit htn H (c := t) (A₀ := A₀) (ε := ε)
    hnd (fun s hs => HS s (hs.trans (hshD.trans hT10'))) htH hcD hLD hlowD hbot' hup
  -- the root's output, copied out
  obtain ⟨hU0, hE0⟩ := hO0 [] 0 ⟨n, A₀, R₀, ε, ℓ₀⟩ rfl rfl
  have hU0' : pairLayout.Holds σu.store p (t + 2) (0 : IExp ℕ).eval r.1 := by
    have e : 2 * (n * n) * 0 + 2 * n * 0 = 0 := by ring
    rw [e] at hU0
    exact hU0
  obtain ⟨hUz, frz, shz, -⟩ := holds_of_exec_zcopy (st := σu) p n n (X := t + 2) (Y := U)
    (xo := 0) (yo := 0) hU0' (el1_bd_ne (by omega)) ((exec_seq_skip I _ _).trans hz)
  obtain ⟨shc, hcp, frc⟩ := ep1_copy_loop (X := t + 4) (Y := dv) (by omega) g25
  refine ⟨shc.trans (shz.trans (hshU.trans (hshD.trans hT10'))),
    el1_holds_keep hUz fun i _ _ => frc p U i (Or.inl hUdv), fun i => ?_⟩
  rw [hcp i i.isLt, frz p (t + 4) i (el1_bd_ne (by omega))]
  have := hE0 i
  simp only [Nat.mul_zero, Nat.zero_add] at this
  exact this

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: an old index below a grown store size. -/
private theorem ep1_lt {S : St P K C} {t m k : ℕ} (h : S.store.size = t + m) (hk : k < m) :
    t + k < S.store.size := by
  rw [h]; exact Nat.add_lt_add_left hk t

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: an old handle below a grown store size. -/
private theorem ep1_lt' {S : St P K C} {t m b : ℕ} (h : S.store.size = t + m) (hb : b < t) :
    b < S.store.size := by
  rw [h]; exact lt_of_lt_of_le hb (Nat.le_add_right _ _)

/-- **The refinement of the spectral bisection program, partial equality**: let the kernels `mm`,
`qr` of `I` be the routines `mmR`, `qrR` on interleaved pairs, and the semantics decide flags at
`p`, with exact integer literals up to $n + 4$ and the exact floor conversion. A successful run of
`NLAlib.eighProg` at size $n$, depth counter $\ell_0$ and step limit $F$, from a state with the tape
positions at $0$, whose block at offset $0$ of `A` holds the stored $\mathbf{A}$ and whose cells
$0$, $1$, $2$ of `par` hold $R_0$, $\varepsilon$, $\beta$, ends with the block at offset $0$ of `U`
and the cells $0, \ldots, n - 1$ of `dv` holding exactly
$$\mathsf{eigh}(\mathbf{A}, R_0, \varepsilon, \beta)$$
computed by `NLAlib.eigh` with step limit $F$ and depth counter $\ell_0$ on the machine of the
interpretation (`NLAlib.eighTapeMachine`), with the tree of samples at the slots
(`NLAlib.eighSlotTree`). [Shah2024, Algorithm 3], for the program. No printed source.
Proof: the scope allocates the constants and the arenas at handles `st.store.size + j`
(`NLAlib.Computation.exec_alloc`), distinct from `A`, `par`, `U`, `dv` (`NLAlib.EighArenas.Shaped`);
the initialisation gives `NLAlib.EighArenas.LevelHolds` at depth $0$ (the root at slot $0$, its size
the literal $n$ read back by `NLAlib.Computation.IsExactIntLit.toNat_eq_of_lit_eq_some`, every
other size $0$, $\mathbf{A}$ by the pilot's `NLAlib.Computation.holds_of_exec_zcopy`); the
downward loop by `NLAlib.Computation.forall_of_exec_loop_eq_some` (pilot) with
`NLAlib.holds_of_exec_eighDownLevel` (the records of depths below $d$ are kept by its frame); then
`NLAlib.holds_of_exec_eighBottomLevel`, and the upward loop with `NLAlib.holds_of_exec_eighUpLevel`
at $d = \ell_0 - d'$; at depth $0$ `NLAlib.EighArenas.OutHolds` is `NLAlib.eighAux` at budget
$\ell_0 + 1$ on the root, which is `NLAlib.eigh`, with the samples
`NLAlib.eighSlotTree M n F R₀ β 0 0 root`; the final copies and the pops. L, about 160 lines.
`NLAlib.holds_of_exec_eighDownLevel` at level $d$ needs `hnext` (the size cells of depth $d + 1$ read
$0$): the initialisation writes the literal $0$ to every size cell and then $n$ to cell $0$ only,
and level $d$ writes only cells of depths $d$ and $d + 1$ (its frame), so the downward loop's
invariant carries "the size cells of every depth $e > d$ read $0$"; and `hc` with its five cells:
$1$, $\mathrm{fl}(2)$, $\mathrm{fl}(1/\mathrm{fl}(2))$, $-1$ and
`NLAlib.Computation.ScalarSem.sqrtHalf` (the square root of cell $2$), from the initialisation and
kept by every level's frame. -/
theorem holds_of_exec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F : ℕ) (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    {A par U dv : ℕ} {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : [A, par, U, dv].Nodup) (hsize : ∀ j ∈ [A, par, U, dv], j < st.store.size)
    (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0)
    (h : exec I (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run st =
      some st') :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M n F R₀ β 0 0 ⟨n, A₀, R₀, ε, ℓ₀⟩)
    pairLayout.Holds st'.store p U 0 r.1 ∧ ∀ i : Fin n, st'.store.read p dv i = some (r.2 i) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hAt := hsize A (by simp)
  have hpart := hsize par (by simp)
  have hUt := hsize U (by simp)
  have hdvt := hsize dv (by simp)
  have hUdv : U ≠ dv := fun h => by simp [h] at hbufs
  set t := st.store.size with ht
  -- the scope and the eleven allocations
  rw [ep1_prog_eq] at h
  rw [exec_seq_skip] at h
  obtain ⟨S1, s1, hS1, hb1, hp1, g1, he1⟩ := ep1_alloc h
  clear h
  obtain ⟨S2, s2, hS2, hb2, hp2, g2, he2⟩ := ep1_alloc g1
  clear g1
  obtain ⟨S3, s3, hS3, hb3, hp3, g3, he3⟩ := ep1_alloc g2
  clear g2
  obtain ⟨S4, s4, hS4, hb4, hp4, g4, he4⟩ := ep1_alloc g3
  clear g3
  obtain ⟨S5, s5, hS5, hb5, hp5, g5, he5⟩ := ep1_alloc g4
  clear g4
  obtain ⟨S6, s6, hS6, hb6, hp6, g6, he6⟩ := ep1_alloc g5
  clear g5
  obtain ⟨S7, s7, hS7, hb7, hp7, g7, he7⟩ := ep1_alloc g6
  clear g6
  obtain ⟨S8, s8, hS8, hb8, hp8, g8, he8⟩ := ep1_alloc g7
  clear g7
  obtain ⟨S9, s9, hS9, hb9, hp9, g9, he9⟩ := ep1_alloc g8
  clear g8
  obtain ⟨S10, s10, hS10, hb10, hp10, g10, he10⟩ := ep1_alloc g9
  clear g9
  obtain ⟨S11, s11, hS11, hb11, hp11, g11, he11⟩ := ep1_alloc g10
  clear g10
  have z1 : S1.store.size = t + 1 := by rw [hS1, Array.size_push]
  have z2 : S2.store.size = t + 2 := by rw [hS2, Array.size_push, z1]
  have z3 : S3.store.size = t + 3 := by rw [hS3, Array.size_push, z2]
  have z4 : S4.store.size = t + 4 := by rw [hS4, Array.size_push, z3]
  have z5 : S5.store.size = t + 5 := by rw [hS5, Array.size_push, z4]
  have z6 : S6.store.size = t + 6 := by rw [hS6, Array.size_push, z5]
  have z7 : S7.store.size = t + 7 := by rw [hS7, Array.size_push, z6]
  have z8 : S8.store.size = t + 8 := by rw [hS8, Array.size_push, z7]
  have z9 : S9.store.size = t + 9 := by rw [hS9, Array.size_push, z8]
  have z10 : S10.store.size = t + 10 := by rw [hS10, Array.size_push, z9]
  have z11 : S11.store.size = t + 11 := by rw [hS11, Array.size_push, z10]
  rw [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10] at g11
  -- the old buffers and the shapes of the new ones
  have hold : ∀ q b i, b < t → S11.store.read q b i = st.store.read q b i := by
    intro q b i hb
    rw [(ep1_push hS11 (b := b) (ep1_lt' z10 hb)).2, (ep1_push hS10 (b := b) (ep1_lt' z9 hb)).2,
      (ep1_push hS9 (b := b) (ep1_lt' z8 hb)).2, (ep1_push hS8 (b := b) (ep1_lt' z7 hb)).2,
      (ep1_push hS7 (b := b) (ep1_lt' z6 hb)).2, (ep1_push hS6 (b := b) (ep1_lt' z5 hb)).2,
      (ep1_push hS5 (b := b) (ep1_lt' z4 hb)).2, (ep1_push hS4 (b := b) (ep1_lt' z3 hb)).2,
      (ep1_push hS3 (b := b) (ep1_lt' z2 hb)).2, (ep1_push hS2 (b := b) (ep1_lt' z1 hb)).2,
      (ep1_push hS1 (b := b) hb).2]
  -- the shapes of the arenas
  simp only [IExp.eval_mul, IExp.eval_add, IExp.eval_const,
    IExp.eval_ofNat] at hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  have hsh1 : S11.store.shape[t + 1]? = S2.store.shape[t + 1]? := by
    rw [(ep1_push hS11 (b := t + 1) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 1) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 1) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 1) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 1) (ep1_lt z6 (by decide))).1,
      (ep1_push hS6 (b := t + 1) (ep1_lt z5 (by decide))).1,
      (ep1_push hS5 (b := t + 1) (ep1_lt z4 (by decide))).1,
      (ep1_push hS4 (b := t + 1) (ep1_lt z3 (by decide))).1,
      (ep1_push hS3 (b := t + 1) (ep1_lt z2 (by decide))).1]
  rw [z1] at hb2
  rw [hb2] at hsh1
  have hsh2 : S11.store.shape[t + 2]? = S3.store.shape[t + 2]? := by
    rw [(ep1_push hS11 (b := t + 2) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 2) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 2) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 2) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 2) (ep1_lt z6 (by decide))).1,
      (ep1_push hS6 (b := t + 2) (ep1_lt z5 (by decide))).1,
      (ep1_push hS5 (b := t + 2) (ep1_lt z4 (by decide))).1,
      (ep1_push hS4 (b := t + 2) (ep1_lt z3 (by decide))).1]
  rw [z2] at hb3
  rw [hb3] at hsh2
  have hsh3 : S11.store.shape[t + 3]? = S4.store.shape[t + 3]? := by
    rw [(ep1_push hS11 (b := t + 3) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 3) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 3) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 3) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 3) (ep1_lt z6 (by decide))).1,
      (ep1_push hS6 (b := t + 3) (ep1_lt z5 (by decide))).1,
      (ep1_push hS5 (b := t + 3) (ep1_lt z4 (by decide))).1]
  rw [z3] at hb4
  rw [hb4] at hsh3
  have hsh4 : S11.store.shape[t + 4]? = S5.store.shape[t + 4]? := by
    rw [(ep1_push hS11 (b := t + 4) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 4) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 4) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 4) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 4) (ep1_lt z6 (by decide))).1,
      (ep1_push hS6 (b := t + 4) (ep1_lt z5 (by decide))).1]
  rw [z4] at hb5
  rw [hb5] at hsh4
  have hsh5 : S11.store.shape[t + 5]? = S6.store.shape[t + 5]? := by
    rw [(ep1_push hS11 (b := t + 5) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 5) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 5) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 5) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 5) (ep1_lt z6 (by decide))).1]
  rw [z5] at hb6
  rw [hb6] at hsh5
  have hsh6 : S11.store.shape[t + 6]? = S7.store.shape[t + 6]? := by
    rw [(ep1_push hS11 (b := t + 6) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 6) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 6) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 6) (ep1_lt z7 (by decide))).1]
  rw [z6] at hb7
  rw [hb7] at hsh6
  have hsh7 : S11.store.shape[t + 7]? = S8.store.shape[t + 7]? := by
    rw [(ep1_push hS11 (b := t + 7) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 7) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 7) (ep1_lt z8 (by decide))).1]
  rw [z7] at hb8
  rw [hb8] at hsh7
  have hsh8 : S11.store.shape[t + 8]? = S9.store.shape[t + 8]? := by
    rw [(ep1_push hS11 (b := t + 8) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 8) (ep1_lt z9 (by decide))).1]
  rw [z8] at hb9
  rw [hb9] at hsh8
  have hg : exec I (do
        ins (.lit p ⟨t, 0⟩ 1)
        ins (.litIdx p ⟨t, 1⟩ 2)
        ins (.bin p .div ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        ins (.un p .neg ⟨t, 3⟩ ⟨t, 0⟩)
        ins (.un p .sqrt ⟨t, 4⟩ ⟨t, 2⟩)
        forRange (.const n * (.const ℓ₀ + 1 + 1) + 1) fun w => ins (.litIdx p ⟨t + 5, .var w⟩ 0)
        ins (.litIdx p ⟨t + 5, 0⟩ (.const n))
        zcopy p (.const n) (.const n) A 0 (t + 1) 0
        ins (.copy p ⟨t + 8, 0⟩ ⟨par, 0⟩)
        ins (.copy p ⟨t + 8, 1⟩ ⟨par, 1⟩)
        forRange (.const ℓ₀ + 1) fun d =>
          eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par (t + 8) (t + 9)
            (t + 10) (t + 1) (t + 2) (t + 3) (t + 4) (t + 5) (t + 6) (t + 7) ⟨t, 0⟩ ⟨t, 1⟩ ⟨t, 2⟩
            ⟨t, 3⟩ ⟨t, 4⟩
        eighBottomLevel p (.const n) (.const ℓ₀ + 1) (t + 2) (t + 4) (t + 5)
        forRange (.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') (t + 8) (t + 2) (t + 3) (t + 4)
            (t + 5) (t + 6) (t + 7) ⟨t, 1⟩
        zcopy p (.const n) (.const n) (t + 2) 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨t + 4, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run S11 = some s11 := g11
  have hS11p : S11.pos = st.pos := by
    rw [hp11, hp10, hp9, hp8, hp7, hp6, hp5, hp4, hp3, hp2, hp1]
  clear g11
  obtain ⟨hshB, hUs, hdvs⟩ := ep1_body hmm hqr p hflag hcmp n ℓ₀ F hn1 hlit htn (A₀ := A₀) hAt hpart
    hUt hdvt hUdv hA hpar hpos hold hS11p hsh1 hsh2 hsh3 hsh4 hsh5 hsh6 hsh7 hsh8 hg
  clear hg
  -- the pops
  have hs11 : s11.store.size = t + 11 := by
    rw [Store.size_eq_of_shape_eq hshB, z11]
  obtain ⟨y10, q10⟩ := ep1_pop (m := t + 10) he11 (by rw [hs11])
  obtain ⟨y9, q9⟩ := ep1_pop (m := t + 9) he10 (by rw [y10])
  obtain ⟨y8, q8⟩ := ep1_pop (m := t + 8) he9 (by rw [y9])
  obtain ⟨y7, q7⟩ := ep1_pop (m := t + 7) he8 (by rw [y8])
  obtain ⟨y6, q6⟩ := ep1_pop (m := t + 6) he7 (by rw [y7])
  obtain ⟨y5, q5⟩ := ep1_pop (m := t + 5) he6 (by rw [y6])
  obtain ⟨y4, q4⟩ := ep1_pop (m := t + 4) he5 (by rw [y5])
  obtain ⟨y3, q3⟩ := ep1_pop (m := t + 3) he4 (by rw [y4])
  obtain ⟨y2, q2⟩ := ep1_pop (m := t + 2) he3 (by rw [y3])
  obtain ⟨y1, q1⟩ := ep1_pop (m := t + 1) he2 (by rw [y2])
  obtain ⟨-, q0⟩ := ep1_pop (m := t) he1 (by rw [y1])
  have hfin : ∀ q b i, b < t → st'.store.read q b i = s11.store.read q b i := by
    intro q b i hb
    have hk : ∀ k, b < t + k := fun k => lt_of_lt_of_le hb (Nat.le_add_right _ _)
    rw [q0 q b i hb, q1 q b i (hk 1), q2 q b i (hk 2), q3 q b i (hk 3), q4 q b i (hk 4),
      q5 q b i (hk 5), q6 q b i (hk 6), q7 q b i (hk 7), q8 q b i (hk 8), q9 q b i (hk 9),
      q10 q b i (hk 10)]
  exact ⟨el1_holds_keep hUs fun i _ _ => hfin p U i hUt,
    fun i => (hfin p dv i hdvt).trans (hdvs i)⟩

/-! #### Helpers of `NLAlib.exists_exec_eighProg` -/

omit [Inhabited K] in
/-- EP2: builders that run the same under continuations that run the same run the same. -/
private theorem ep2_run_eq {X Y : Builder P ι ℕ ℕ Unit} (h : el1_Equiv I X Y) (st : St P K C) :
    exec I X.run st = exec I Y.run st :=
  h (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

set_option maxHeartbeats 8000000 in
-- The walk goes through every statement of the level, its leaves and its node step.
omit [Inhabited K] in
/-- EP2: a level of the downward pass at an index variable runs as at the constant of its value. -/
private theorem ep2_down_congr (p : P) (mm qr : ι) (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp
    c : ℕ) (st : St P K C) :
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st := by
  refine ep2_run_eq ?_ st
  unfold eighDownLevel
  repeat' first
    | rfl
    | exact el1E_pure
    | apply el1E_ins
    | apply el1E_kcall
    | apply el1E_forRange
    | apply el1E_bindIdx
    | apply el1E_ite
    | apply el1E_named
    | apply el1E_scope
    | apply el1E_allocBind
    | apply el1E_bind
    | intro _

set_option maxHeartbeats 4000000 in
-- The walk goes through every statement of the level.
omit [Inhabited K] in
/-- EP2: a level of the upward pass at $\ell_0 - j$ runs as at the constant of its value. -/
private theorem ep2_up_congr (p : P) (mm : ι) (n ℓ₀ j Lv Ua Qa Ea Sz Kd Kp c : ℕ)
    (st : St P K C) :
    exec I (eighUpLevel p mm (.const n) (.const ℓ₀ - .var j) Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run st =
      exec I (eighUpLevel p mm (.const n) (.const (ℓ₀ - j)) Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run
        st := by
  refine ep2_run_eq ?_ st
  unfold eighUpLevel
  repeat' first
    | rfl
    | exact el1E_pure
    | apply el1E_ins
    | apply el1E_kcall
    | apply el1E_forRange
    | apply el1E_bindIdx
    | apply el1E_ite
    | apply el1E_named
    | apply el1E_scope
    | apply el1E_allocBind
    | apply el1E_bind
    | intro _

omit [Inhabited K] in
/-- EP2: the spent level at depth $\ell_0 + 1$ runs as at the constant of its value. -/
private theorem ep2_bot_congr (p : P) (n ℓ₀ Ua Ea Sz : ℕ) (st : St P K C) :
    exec I (eighBottomLevel (ι := ι) p (.const n) (.const ℓ₀ + 1) Ua Ea Sz).run st =
      exec I (eighBottomLevel (ι := ι) p (.const n) (.const (ℓ₀ + 1)) Ua Ea Sz).run st := by
  refine ep2_run_eq ?_ st
  unfold eighBottomLevel
  repeat' first
    | rfl
    | exact el1E_pure
    | apply el1E_ins
    | apply el1E_kcall
    | apply el1E_forRange
    | apply el1E_bindIdx
    | apply el1E_ite
    | apply el1E_named
    | apply el1E_scope
    | apply el1E_allocBind
    | apply el1E_bind
    | intro _

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP2: the slots of the nodes lie in $[0, n]$ (also for $n = 0$), and the nodes are not empty
when $n \ge 1$. -/
private theorem ep2_bnd {M : FloatMachine K ℕ ℕ} {n F : ℕ} {R₀ β ε : K} {ℓ₀ : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)} {a : List Bool} {lo : ℕ} {y : EighNode K}
    (h : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) :
    lo + y.k ≤ n ∧ (1 ≤ n → 1 ≤ y.k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨?_, fun h => absurd h (by omega)⟩
    cases a with
    | nil => cases h; rfl
    | cons b a => simp [eighLoc, eighStep] at h
  · exact ⟨(eighLoc_bounds hn h).2, fun _ => (eighLoc_bounds hn h).1⟩

/-- EP2: a cell of a depth lies in one of the arenas. -/
private theorem ep2_lc_mem {H : EighArenas} {n e b i : ℕ} (h : H.LevelCell n e b i) :
    b ∈ H.handles := by
  unfold EighArenas.LevelCell at h
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ⟨h | h | h, -⟩ | ⟨h | h | h | h, -⟩ | ⟨h, -⟩ <;> simp [h]

/-- EP2: two intervals of one length at distinct multiples are disjoint. -/
private theorem ep2_iv {m e e' i : ℕ} (h1 : m * e ≤ i) (h2 : i < m * (e + 1)) (h3 : m * e' ≤ i)
    (h4 : i < m * (e' + 1)) : e = e' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := Nat.mul_le_mul_left m (show e + 1 ≤ e' by omega); omega
  · have := Nat.mul_le_mul_left m (show e' + 1 ≤ e by omega); omega

/-- EP2: the cells of distinct depths are distinct. -/
private theorem ep2_lc_ne {H : EighArenas} (hnd : H.handles.Nodup) {n e e' b i : ℕ} (hne : e ≠ e')
    (h : H.LevelCell n e b i) : ¬ H.LevelCell n e' b i := by
  intro h'
  unfold EighArenas.LevelCell at h h'
  rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1⟩ <;>
    rcases h' with ⟨hb', h1', h2'⟩ | ⟨hb', h1', h2'⟩ | ⟨hb', h1'⟩
  · exact hne (ep2_iv (m := 2 * (n * n)) h1 h2 h1' h2')
  · rcases hb with rfl | rfl | rfl <;> rcases hb' with h | h | h | h <;>
      simp [EighArenas.handles, h] at hnd
  · rcases hb with rfl | rfl | rfl <;> simp [EighArenas.handles, hb'] at hnd
  · rcases hb with rfl | rfl | rfl | rfl <;> rcases hb' with h | h | h <;>
      simp [EighArenas.handles, h] at hnd
  · exact hne (ep2_iv (m := n) h1 h2 h1' h2')
  · rcases hb with rfl | rfl | rfl | rfl <;> simp [EighArenas.handles, hb'] at hnd
  · subst hb; rcases hb' with h | h | h <;> simp [EighArenas.handles, h] at hnd
  · subst hb; rcases hb' with h | h | h | h <;> simp [EighArenas.handles, h] at hnd
  · omega

/-- EP2: a block of a node of depth $e$ lies in the block of depth $e$. -/
private theorem ep2_blk {n e lo k i : ℕ} (hk : lo + k ≤ n) (h1 : 2 * (n * n) * e + 2 * n * lo ≤ i)
    (h2 : i < 2 * (n * n) * e + 2 * n * lo + 2 * (k * k)) :
    2 * (n * n) * e ≤ i ∧ i < 2 * (n * n) * (e + 1) := by
  have e1 : 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) := by nlinarith
  have e2 : 2 * (n * n) * (e + 1) = 2 * (n * n) * e + 2 * (n * n) := by ring
  omega

omit [AddMonoid C] [Inhabited K] in
/-- EP2: the nodes of a depth transfer to a store that reads the same on the sizes, node matrices
and parameters of that depth (and on the size cell $ne$, the root's when $n = 0$). -/
private theorem ep2_lev_tr {H : EighArenas} {s s' : Store P K} {p : P} {sem : ScalarSem P K}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ e : ℕ} {R₀ β ε : K} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hs : ∀ q b i, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) →
      (H.LevelCell n e b i ∨ (b = H.Sz ∧ i = n * e)) → s'.read q b i = s.read q b i)
    (h : H.LevelHolds sem s p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e) :
    H.LevelHolds sem s' p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e := by
  have e4 : n * (e + 1) = n * e + n := by ring
  refine ⟨fun a lo y ha hay => ?_, fun lo hlo hno => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 a lo y ha hay
    obtain ⟨hb, hb1⟩ := ep2_bnd hay
    refine ⟨el1_readsIdx_congr (hs p _ _ (Or.inr (Or.inl rfl)) ?_) h1,
      el1_holds_keep h2 fun i h1' h2' => hs p _ _ (Or.inl rfl) ?_⟩
    · by_cases hlo : lo = 0
      · exact Or.inr ⟨rfl, by omega⟩
      · have := hb1 (by omega)
        exact Or.inl (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by omega⟩))
    · exact Or.inl (Or.inl ⟨Or.inl rfl, ep2_blk hb h1' h2'⟩)
  · exact el1_readsIdx_congr (hs p _ _ (Or.inr (Or.inl rfl))
      (Or.inl (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by omega⟩)))) (h.2.1 lo hlo hno)
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inl (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)))]
    exact h.2.2.1
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inl (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)))]
    exact h.2.2.2

omit [AddMonoid C] [Inhabited K] in
/-- EP2: the records of a depth transfer to a store that reads the same on the cells of that
depth. -/
private theorem ep2_rec_tr {H : EighArenas} {s s' : Store P K} {p : P} {sem : ScalarSem P K}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ e : ℕ} {R₀ β ε : K} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hs : ∀ q b i, H.LevelCell n e b i → s'.read q b i = s.read q b i)
    (h : H.RecordHolds sem s p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e) :
    H.RecordHolds sem s' p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e := by
  have e4 : n * (e + 1) = n * e + n := by ring
  intro a lo y ha hay hk
  have h0 := h a lo y ha hay hk
  have hb := (ep2_bnd hay).1
  have hlo1 : n * e ≤ n * e + lo := by omega
  have hlo2 : n * e + lo < n * (e + 1) := by omega
  have hK : ∀ {b k}, (b = H.Ea ∨ b = H.Sz ∨ b = H.Kd ∨ b = H.Kp) →
      ReadsIdx sem s p b (n * e + lo) k → ReadsIdx sem s' p b (n * e + lo) k := fun hb' hr =>
    el1_readsIdx_congr (hs p _ _ (Or.inr (Or.inl ⟨hb', hlo1, hlo2⟩))) hr
  rcases hst : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n e lo) with
    ⟨U, ee⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩ <;> rw [hst] at h0 <;> dsimp only at h0 ⊢
  · obtain ⟨h1, h2, h3⟩ := h0
    refine ⟨hK (Or.inr (Or.inr (Or.inl rfl))) h1, el1_holds_keep h2 fun i h1' h2' => hs p _ _
      (Or.inl ⟨Or.inr (Or.inl rfl), ep2_blk hb h1' h2'⟩), fun i => ?_⟩
    have := i.isLt
    rw [hs p _ _ (Or.inr (Or.inl ⟨Or.inl rfl, by omega, by omega⟩))]
    exact h3 i
  · exact hK (Or.inr (Or.inr (Or.inl rfl))) h0
  · obtain ⟨h1, h2, h3, h4⟩ := h0
    have hkk : y.k * kp + y.k * (y.k - kp) = y.k * y.k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hkp]
    have hkk' : y.k * kp ≤ y.k * y.k := Nat.mul_le_mul_left _ hkp
    refine ⟨hK (Or.inr (Or.inr (Or.inl rfl))) h1, hK (Or.inr (Or.inr (Or.inr rfl))) h2,
      el1_holds_keep h3 fun i h1' h2' => hs p _ _
        (Or.inl ⟨Or.inr (Or.inr rfl), ep2_blk hb h1' (by omega)⟩),
      el1_holds_keep h4 fun i h1' h2' => hs p _ _
        (Or.inl ⟨Or.inr (Or.inr rfl), ep2_blk hb (by omega) (by omega)⟩)⟩

/-- EP2: the cells $0$ to $4$ of `c` hold the constants of `NLAlib.eighProg` (one, $\mathrm{fl}(2)$,
$\mathrm{fl}(1/2)$, $-1$, the stored $\sqrt{1/2}$). -/
private def ep2_cst (I : Interp P ι K C) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K))
    (s : Store P K) (p : P) (c : ℕ) : Prop :=
  s.read p c 0 = I.sem.lit p 1 ∧ s.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
    s.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
      (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
    s.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg (eighTapeMachine I p mmR qrR).one) ∧
    s.read p c 4 = some (I.sem.sqrtHalf p)

omit [AddMonoid C] in
/-- EP2: the constants are kept by a store that reads as `s` on `c`. -/
private theorem ep2_cst_congr {s s' : Store P K} {p : P} {c : ℕ}
    (hs : ∀ i, s'.read p c i = s.read p c i) (h : ep2_cst I mmR qrR s p c) :
    ep2_cst I mmR qrR s' p c := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨(hs 0).trans h0, (hs 1).trans h1, (hs 2).trans h2, (hs 3).trans h3, (hs 4).trans h4⟩

/-- EP2: a buffer outside the arenas is not one of them. -/
private theorem ep2_out {H : EighArenas} {l : List ℕ} (h : (H.handles ++ l).Nodup) {x : ℕ}
    (hx : x ∈ l) : x ∉ H.handles := fun hm => List.disjoint_of_nodup_append h hm hx

/-- EP2: the sizes, node matrices and parameters are not records. -/
private theorem ep2_msl {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (hb : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) :
    ¬ (b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) := by
  intro h
  rcases hb with rfl | rfl | rfl <;> rcases h with h | h | h | h | h <;>
    simp [EighArenas.handles, h] at hnd

/-- EP2: the size cell $ne$ is not a cell of a deeper depth. -/
private theorem ep2_sz_lc {H : EighArenas} (hnd : H.handles.Nodup) {n e d : ℕ} (he : e < d) :
    ¬ H.LevelCell n d H.Sz (n * e) := by
  unfold EighArenas.LevelCell
  rintro (⟨hb, -⟩ | ⟨-, h1, h2⟩ | ⟨hb, -⟩)
  · rcases hb with h | h | h <;> simp [EighArenas.handles, h] at hnd
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at h2
    · have := Nat.mul_le_mul_left n (show e + 1 ≤ d by omega)
      have : n * (e + 1) = n * e + n := by ring
      omega
  · simp [EighArenas.handles, hb] at hnd

/-- EP2: a size cell at or past depth $d + 1$ is not a cell of depth $d$. -/
private theorem ep2_sz_ge {H : EighArenas} (hnd : H.handles.Nodup) {n d j : ℕ}
    (hj : n * (d + 1) ≤ j) : ¬ H.LevelCell n d H.Sz j := by
  unfold EighArenas.LevelCell
  rintro (⟨hb, -⟩ | ⟨-, h1, h2⟩ | ⟨hb, -⟩)
  · rcases hb with h | h | h <;> simp [EighArenas.handles, h] at hnd
  · omega
  · simp [EighArenas.handles, hb] at hnd

/-- EP2: a cell the node transfer reads is not a cell of a deeper depth. -/
private theorem ep2_msl_lc {H : EighArenas} (hnd : H.handles.Nodup) {n e d b i : ℕ} (he : e < d)
    (hi : H.LevelCell n e b i ∨ (b = H.Sz ∧ i = n * e)) : ¬ H.LevelCell n d b i := by
  rcases hi with hi | ⟨rfl, rfl⟩
  · exact ep2_lc_ne hnd (by omega) hi
  · exact ep2_sz_lc hnd he

omit [Inhabited K] in
/-- EP2: a builder that emits one statement, then the rest, succeeds when both parts do. -/
private theorem ep2_ex_bind {b : Builder P ι ℕ ℕ Unit} {X : Stmt P ι ℕ ℕ}
    {f : Unit → Builder P ι ℕ ℕ Unit} {st s₁ : St P K C} (h₁ : exec I b.run st = some s₁)
    (h₂ : ∃ st', exec I (f ()).run s₁ = some st') (hb : ∀ k, ContT.run b k = .seq X (k ())) :
    ∃ st', exec I (b >>= f).run st = some st' := by
  rw [exec_run_bind I hb f st, h₁, Option.bind_some]
  exact h₂

set_option maxHeartbeats 1600000 in
-- The invariant of the downward pass has seven parts.
/-- EP2: the downward pass succeeds and ends with the nodes of every depth $\le \ell_0 + 1$ and the
records of every depth $\le \ell_0$; the shape and every cell outside the arenas and the sample
buffers are kept. -/
private theorem ep2_down {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (hℓ : 1 ≤ ℓ₀)
    (H : EighArenas) {par Su Sg c : ℕ} {σ : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hH : H.Shaped σ.store p n (ℓ₀ + 1)) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ 0)
    (hz : ∀ j, n ≤ j → j < n * (ℓ₀ + 1 + 1) → ReadsIdx I.sem σ.store p H.Sz j 0)
    (hpos : σ.pos .uniform = 0 ∧ σ.pos .gaussian = 0)
    (hpar : σ.store.read p par 0 = some R₀ ∧ σ.store.read p par 2 = some β)
    (hSu : ∃ len, σ.store.shape[Su]? = some (p, len) ∧ n ≤ len)
    (hSg : ∃ len, σ.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len)
    (hc : ep2_cst I mmR qrR σ.store p c) :
    ∃ σ' : St P K C, exec I (.loop (IExp.const ℓ₀ + 1) fun d => (eighDownLevel p mm qr (.const n)
        (.const ℓ₀) (.const F) (.var d) par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩
        ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run) σ = some σ' ∧
      σ'.store.shape = σ.store.shape ∧
      (∀ q b i, b ∉ H.handles → b ≠ Su → b ≠ Sg → σ'.store.read q b i = σ.store.read q b i) ∧
      (∀ e ≤ ℓ₀ + 1, H.LevelHolds I.sem σ'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ e < ℓ₀ + 1, H.RecordHolds I.sem σ'.store p (eighTapeMachine I p mmR qrR) n F R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) := by
  have hnd := hH.1
  have hflag : I.sem.DecidesFlags p := el2_flags hsem hlit (by omega) p
  have hcmp := hsem.cmp_le p
  have hpo := ep2_out hbufs (x := par) (by simp)
  have hco := ep2_out hbufs (x := c) (by simp)
  have dSuSg : Su ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSu : par ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSg : par ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSu : c ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSg : c ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have hSuo := ep2_out hbufs (x := Su) (by simp)
  have hSgo := ep2_out hbufs (x := Sg) (by simp)
  have hhS : ∀ {b}, b ∈ H.handles → b ≠ Su ∧ b ≠ Sg := fun hb =>
    ⟨fun h => hSuo (h ▸ hb), fun h => hSgo (h ▸ hb)⟩
  have hmsl : ∀ {b}, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → b ∈ H.handles := fun hb => by
    rcases hb with rfl | rfl | rfl <;> simp [EighArenas.handles]
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := IExp.const ℓ₀ + 1)
    (fun d (s : St P K C) => s.store.shape = σ.store.shape ∧ s.pos .uniform = n * d ∧
      s.pos .gaussian = 4 * (n * n) * d ∧
      (∀ q b i, b ∉ H.handles → b ≠ Su → b ≠ Sg → s.store.read q b i = σ.store.read q b i) ∧
      (∀ e ≤ d, H.LevelHolds I.sem s.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ e < d, H.RecordHolds I.sem s.store p (eighTapeMachine I p mmR qrR) n F R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      ∀ j, n * (d + 1) ≤ j → j < n * (ℓ₀ + 1 + 1) → ReadsIdx I.sem s.store p H.Sz j 0)
    ⟨rfl, by rw [hpos.1]; ring, by rw [hpos.2]; ring, fun _ _ _ _ _ _ => rfl,
      fun e he => by obtain rfl : e = 0 := (by omega); exact hlev,
      fun e he => absurd he (Nat.not_lt_zero _), fun j hj => hz j (by simpa using hj)⟩ ?_).elim
    fun σ' h => ⟨σ', h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  rintro d hd s ⟨hsh, hpu, hpg, hfr, hlv, hrc, hzs⟩
  change d < ℓ₀ + 1 at hd
  have hHs : H.Shaped s.store p n (ℓ₀ + 1) :=
    el1_shaped_of_eq (fun b _ => by rw [hsh]) hH
  have hpar' : s.store.read p par 0 = some R₀ ∧ s.store.read p par 2 = some β :=
    ⟨(hfr _ _ _ hpo dparSu dparSg).trans hpar.1, (hfr _ _ _ hpo dparSu dparSg).trans hpar.2⟩
  have hcs : ep2_cst I mmR qrR s.store p c :=
    ep2_cst_congr (fun i => hfr _ _ _ hco dcSu dcSg) hc
  have hSu' : ∃ len, s.store.shape[Su]? = some (p, len) ∧ n ≤ len := by rw [hsh]; exact hSu
  have hSg' : ∃ len, s.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len := by
    rw [hsh]; exact hSg
  obtain ⟨s', hs'⟩ := exists_exec_eighDownLevel hmm hqr hsem p hu n ℓ₀ F d (ℓ₀ + 1) hd hℓ hlit
    htn H hε hR₀ hHs hbufs (hlv d le_rfl) hpar' hSu' hSg' ⟨hpu, hpg⟩ hcs
  have hnext : ∀ lo < n, ReadsIdx I.sem s.store p H.Sz (n * (d + 1) + lo) 0 := fun lo hlo =>
    hzs _ (by omega) (by
      have := Nat.mul_le_mul_left n (show d + 1 + 1 ≤ ℓ₀ + 1 + 1 by omega)
      have : n * (d + 1 + 1) = n * (d + 1) + n := by ring
      omega)
  obtain ⟨L1, R1, F1, S1, P1, P2⟩ := ep2_holds_of_exec_eighDownLevel hmm hqr p hflag hcmp n ℓ₀ F d
    (ℓ₀ + 1) hd hlit htn H hHs hbufs (hlv d le_rfl) hnext ⟨hpu, hpg⟩ hpar' hcs hs'
  refine ⟨s', (ep2_down_congr p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c
    s).trans hs', S1.trans hsh, by rw [P1, hpu]; ring, by rw [P2, hpg]; ring,
    fun q b i hb h1 h2 => ?_, fun e he => ?_, fun e he => ?_, fun j hj1 hj2 => ?_⟩
  · exact (F1 q b i h1 h2 (fun h => hb (ep2_lc_mem h.2)) (fun h => hb (ep2_lc_mem h))).trans
      (hfr q b i hb h1 h2)
  · rcases Nat.lt_or_ge e (d + 1) with he' | he'
    · refine ep2_lev_tr (fun q b i hb hi => F1 q b i (hhS (hmsl hb)).1 (hhS (hmsl hb)).2
        (fun h => ep2_msl hnd hb h.1) (ep2_msl_lc hnd he' hi)) (hlv e (by omega))
    · obtain rfl : e = d + 1 := by omega
      exact L1
  · rcases Nat.lt_or_ge e d with he' | he'
    · refine ep2_rec_tr (fun q b i hi => F1 q b i (hhS (ep2_lc_mem hi)).1
        (hhS (ep2_lc_mem hi)).2 (fun h => ep2_lc_ne hnd (by omega) hi h.2)
        (ep2_lc_ne hnd (by omega) hi)) (hrc e he')
    · obtain rfl : e = d := by omega
      exact R1
  · have hSzh : H.Sz ∈ H.handles := hmsl (Or.inr (Or.inl rfl))
    refine el1_readsIdx_congr (F1 p H.Sz j (hhS hSzh).1 (hhS hSzh).2
      (fun h => ep2_msl hnd (Or.inr (Or.inl rfl)) h.1) (ep2_sz_ge hnd hj1)) (hzs j ?_ hj2)
    have := Nat.mul_le_mul_left n (show d + 1 ≤ d + 1 + 1 by omega)
    omega

set_option maxHeartbeats 800000 in
-- The invariant of the upward pass has five parts.
/-- EP2: the upward pass succeeds and ends with the outputs of depth $0$; the shape and every
cell outside the arenas are kept. -/
private theorem ep2_up {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {c : ℕ} {σ : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped σ.store p n (ℓ₀ + 1)) (hco : c ∉ H.handles)
    (htwov : σ.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : ∀ e < ℓ₀ + 1, H.LevelHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ e)
    (hrec : ∀ e < ℓ₀ + 1, H.RecordHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ e)
    (hout : H.OutHolds σ.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1)) :
    ∃ σ' : St P K C, exec I (.loop (IExp.const ℓ₀ + 1) fun j => (eighUpLevel p mm (.const n)
        (.const ℓ₀ - .var j) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 1⟩).run) σ = some σ' ∧
      σ'.store.shape = σ.store.shape ∧
      (∀ q b i, b ∉ H.handles → σ'.store.read q b i = σ.store.read q b i) ∧
      H.OutHolds σ'.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ 0 := by
  have hnd := hH.1
  have hmsl : ∀ {b}, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → ¬ (b = H.Ua ∨ b = H.Ea) :=
    fun hb h => ep2_msl hnd hb (h.elim (fun h => Or.inr (Or.inl h))
      (fun h => Or.inr (Or.inr (Or.inl h))))
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := IExp.const ℓ₀ + 1)
    (fun j (s : St P K C) => s.store.shape = σ.store.shape ∧
      (∀ q b i, b ∉ H.handles → s.store.read q b i = σ.store.read q b i) ∧
      (∀ e < ℓ₀ + 1 - j, H.LevelHolds I.sem s.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ e < ℓ₀ + 1 - j, H.RecordHolds I.sem s.store p (eighTapeMachine I p mmR qrR) n F R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      H.OutHolds s.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩
        (ℓ₀ + 1 - j))
    ⟨rfl, fun _ _ _ _ => rfl, hlev, hrec, hout⟩ ?_).elim
    fun σ' h => ⟨σ', h.1, h.2.1, h.2.2.1, by
      have h5 := h.2.2.2.2.2
      rwa [show (IExp.const ℓ₀ + 1 : IExp ℕ).eval = ℓ₀ + 1 from rfl, Nat.sub_self] at h5⟩
  rintro j hj s ⟨hsh, hfr, hlv, hrc, hot⟩
  change j < ℓ₀ + 1 at hj
  have e1 : ℓ₀ + 1 - j = ℓ₀ - j + 1 := by omega
  have e2 : ℓ₀ + 1 - (j + 1) = ℓ₀ - j := by omega
  rw [e1] at hlv hrc hot
  rw [e2]
  have hHs : H.Shaped s.store p n (ℓ₀ + 1) := el1_shaped_of_eq (fun b _ => by rw [hsh]) hH
  have htw : s.store.read p (⟨c, 1⟩ : Cell ℕ ℕ).buf (⟨c, 1⟩ : Cell ℕ ℕ).idx.eval =
      I.sem.lit p ((2 : ℕ) : ℚ) := (hfr p c 1 hco).trans htwov
  obtain ⟨s', hs'⟩ := exists_exec_eighUpLevel hmm hsem p n ℓ₀ F (ℓ₀ - j) (ℓ₀ + 1) (by omega)
    hlit htn H (two := ⟨c, 1⟩) hHs hco htw (hlv _ (by omega)) (hrc _ (by omega)) hot
  obtain ⟨O1, F1, S1, -⟩ := holds_of_exec_eighUpLevel hmm p n ℓ₀ F (ℓ₀ - j) (ℓ₀ + 1) (by omega)
    hlit htn H (two := ⟨c, 1⟩) hHs hco htw (hlv _ (by omega)) (hrc _ (by omega)) hot hs'
  refine ⟨s', (ep2_up_congr p mm n ℓ₀ j H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c s).trans hs',
    S1.trans hsh, fun q b i hb => (F1 q b i fun h => hb (ep2_lc_mem h.2)).trans (hfr q b i hb),
    fun e he => ep2_lev_tr (fun q b i hb _ => F1 q b i fun h => hmsl hb h.1) (hlv e (by omega)),
    fun e he => ep2_rec_tr (fun q b i hi => F1 q b i fun h => ep2_lc_ne hnd (by omega) hi h.2)
      (hrc e (by omega)), O1⟩

set_option maxHeartbeats 1600000 in
-- The tail runs the two passes, the spent level and the final copies.
/-- EP2: from the initialised arenas, the two passes, the spent level and the final copies of
`NLAlib.eighProg` succeed. -/
private theorem ep2_tail {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (hℓ : 1 ≤ ℓ₀)
    (H : EighArenas) {par Su Sg c U dv : ℕ} {σ : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hH : H.Shaped σ.store p n (ℓ₀ + 1)) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hUo : U ∉ H.handles) (hdvo : dv ∉ H.handles)
    (hlev : H.LevelHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ 0)
    (hz : ∀ j, n ≤ j → j < n * (ℓ₀ + 1 + 1) → ReadsIdx I.sem σ.store p H.Sz j 0)
    (hpos : σ.pos .uniform = 0 ∧ σ.pos .gaussian = 0)
    (hpar : σ.store.read p par 0 = some R₀ ∧ σ.store.read p par 2 = some β)
    (hSu : ∃ len, σ.store.shape[Su]? = some (p, len) ∧ n ≤ len)
    (hSg : ∃ len, σ.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len)
    (hc : ep2_cst I mmR qrR σ.store p c)
    (hU : ∃ len, σ.store.shape[U]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hdv : ∃ len, σ.store.shape[dv]? = some (p, len) ∧ n ≤ len) :
    ∃ st', exec I (Builder.run (ι := ι) (do
      forRange (IExp.const ℓ₀ + 1) fun d =>
        eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par H.Lv Su Sg H.Ma H.Ua
          H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
      eighBottomLevel p (.const n) (IExp.const ℓ₀ + 1) H.Ua H.Ea H.Sz
      forRange (IExp.const ℓ₀ + 1) fun d' =>
        eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 1⟩
      zcopy p (.const n) (.const n) H.Ua 0 U 0
      forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨H.Ea, .var i⟩))) σ = some st' := by
  have hnd := hH.1
  have hco := ep2_out hbufs (x := c) (by simp)
  have dcSu : c ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSg : c ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have hmsl : ∀ {b}, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → ¬ (b = H.Ua ∨ b = H.Ea) :=
    fun hb h => ep2_msl hnd hb (h.elim (fun h => Or.inr (Or.inl h))
      (fun h => Or.inr (Or.inr (Or.inl h))))
  have hUUa : U ≠ H.Ua := fun h => hUo (h ▸ by simp [EighArenas.handles])
  have hEaU : H.Ea ≠ U := fun h => hUo (h ▸ by simp [EighArenas.handles])
  have hEadv : H.Ea ≠ dv := fun h => hdvo (h ▸ by simp [EighArenas.handles])
  -- the downward pass
  obtain ⟨σ2, h2, hsh2, hfr2, hlv2, hrc2⟩ := ep2_down hmm hqr hsem p hu n ℓ₀ F hlit htn hℓ H hε
    hR₀ hH hbufs hlev hz hpos hpar hSu hSg hc
  refine ep2_ex_bind (by exact (exec_seq_skip I _ _).trans h2) ?_ (by intro _; rfl)
  -- the spent level
  have hH2 : H.Shaped σ2.store p n (ℓ₀ + 1) := el1_shaped_of_eq (fun b _ => by rw [hsh2]) hH
  obtain ⟨σb, hb⟩ := exists_exec_eighBottomLevel (ι := ι) hsem htn p n ℓ₀ F (ℓ₀ + 1) H hH2
    (hlv2 _ le_rfl)
  obtain ⟨Ob, Fb, Sb, -⟩ := holds_of_exec_eighBottomLevel p n ℓ₀ F (ℓ₀ + 1) hlit htn H hH2
    (hlv2 _ le_rfl) hb
  refine ep2_ex_bind (by exact (ep2_bot_congr p n ℓ₀ H.Ua H.Ea H.Sz σ2).trans hb) ?_
    (by intro _; rfl)
  -- the upward pass
  have hHb : H.Shaped σb.store p n (ℓ₀ + 1) := el1_shaped_of_eq (fun b _ => by rw [Sb]) hH2
  obtain ⟨σ3, h3, hsh3, -, hout3⟩ := ep2_up hmm hsem p n ℓ₀ F hlit htn H hHb hco
    ((Fb p c 1 fun h => hco (ep2_lc_mem h.2)).trans ((hfr2 p c 1 hco dcSu dcSg).trans hc.2.1))
    (fun e he => ep2_lev_tr (fun q b i hb _ => Fb q b i fun h => hmsl hb h.1) (hlv2 e (by omega)))
    (fun e he => ep2_rec_tr (fun q b i hi => Fb q b i fun h => ep2_lc_ne hnd (by omega) hi h.2)
      (hrc2 e he)) Ob
  refine ep2_ex_bind (by exact (exec_seq_skip I _ _).trans h3) ?_ (by intro _; rfl)
  -- the copies of the root's output
  have hroot := hout3 [] 0 ⟨n, A₀, R₀, ε, ℓ₀⟩ rfl rfl
  have hU0 := hroot.1
  simp only [Nat.mul_zero, Nat.add_zero] at hU0
  have hsh3' : σ3.store.shape = σ.store.shape := hsh3.trans (Sb.trans hsh2)
  obtain ⟨len, hUs, hUlen⟩ := hU
  obtain ⟨σ4, h4⟩ := exists_exec_zcopy (ι := ι) p n n (X := H.Ua) (xo := 0) (Y := U) (yo := 0)
    hU0 (el1_bd_ne hUUa) ⟨len, by rw [hsh3']; exact hUs, by change 0 + 2 * (n * n) ≤ len; omega⟩
  obtain ⟨-, F4, S4, -⟩ := holds_of_exec_zcopy p n n hU0 (el1_bd_ne hUUa) h4
  refine ep2_ex_bind (by exact h4) ?_ (by intro _; rfl)
  obtain ⟨ldv, hdvs, hdvlen⟩ := hdv
  have hstep : ∀ i < (IExp.const n).eval, ∀ s : St P K C,
      (s.store.shape = σ4.store.shape ∧
        ∀ i, s.store.read p H.Ea i = σ4.store.read p H.Ea i) →
      ∃ s', exec I (Builder.ins (ι := ι) (.copy p ⟨dv, .var i⟩ ⟨H.Ea, .var i⟩)).run s = some s' ∧
        (s'.store.shape = σ4.store.shape ∧
          ∀ i, s'.store.read p H.Ea i = σ4.store.read p H.Ea i) := by
    rintro i hi s ⟨hsh, hE⟩
    change i < n at hi
    obtain ⟨v, hv⟩ : ∃ v, s.store.read p H.Ea i = some v := by
      have := hroot.2 ⟨i, hi⟩
      simp only [Nat.mul_zero, Nat.zero_add] at this
      exact ⟨_, (hE i).trans ((F4 p H.Ea i (el1_bd_ne hEaU)).trans this)⟩
    obtain ⟨s', hw⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := i) v
      (by rw [hsh, S4, hsh3']; exact hdvs) (by omega)
    refine ⟨_, (exec_seq_instr_copy I (dst := ⟨dv, .var i⟩) (src := ⟨H.Ea, .var i⟩) hv hw).trans
      (exec_skip I _), (Store.shape_of_write_eq_some hw).trans hsh, fun j => ?_⟩
    exact (Store.read_of_write_eq_some_of_ne hw (Or.inl hEadv)).trans (hE j)
  obtain ⟨σ5, h5, -⟩ := exists_exec_loop_eq_some_of_forall (I := I) _ ⟨rfl, fun _ => rfl⟩ hstep
  exact ⟨σ5, (exec_seq_skip I _ _).trans h5⟩

omit [Inhabited K] in
/-- EP2: a literal, then the rest. -/
private theorem ep2_ex_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {v : K} {s' : Store P K} (hv : I.sem.lit p q = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some st') :
    ∃ st', exec I (.seq (.instr (.lit p dst q)) t) s = some st' := by
  rw [exec_seq_instr_lit I hv hw]
  exact h

omit [Inhabited K] in
/-- EP2: a unary operation, then the rest. -/
private theorem ep2_ex_un {p : P} {o : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {a v : K} {s' : Store P K} (hx : s.store.read p x.buf x.idx.eval = some a)
    (hv : I.sem.un p o a = some v) (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.un p o) } = some st') :
    ∃ st', exec I (.seq (.instr (.un p o dst x)) t) s = some st' := by
  rw [exec_seq_instr_un I hx hv hw]
  exact h

omit [Inhabited K] in
/-- EP2: a copy, then the rest. -/
private theorem ep2_ex_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {v : K} {s' : Store P K} (hx : s.store.read p src.buf src.idx.eval = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.copy p) } = some st') :
    ∃ st', exec I (.seq (.instr (.copy p dst src)) t) s = some st' := by
  rw [exec_seq_instr_copy I hx hw]
  exact h

omit [Inhabited K] in
/-- EP2: a loop writing the index literal $0$ into the first cells of a buffer succeeds; those
cells hold it, and the shape, the tape positions and the other buffers are kept. -/
private theorem ep2_lits {p : P} {m : IExp ℕ} {Y len : ℕ} {z : K} {st : St P K C}
    (hz : I.sem.lit p (((0 : IExp ℕ).eval : ℕ) : ℚ) = some z)
    (hY : st.store.shape[Y]? = some (p, len)) (hm : m.eval ≤ len) :
    ∃ st' : St P K C, exec I (.loop m fun w =>
        (Builder.ins (ι := ι) (.litIdx p ⟨Y, .var w⟩ 0)).run) st = some st' ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ j < m.eval, st'.store.read p Y j = some z) ∧
      ∀ q b i, b ≠ Y → st'.store.read q b i = st.store.read q b i := by
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := m)
    (fun w (s : St P K C) => s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
      (∀ j < w, s.store.read p Y j = some z) ∧
      ∀ q b i, b ≠ Y → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_).elim
    fun σ' h => ⟨σ', h.1, h.2⟩
  rintro w hw s ⟨hsh, hps, hY', hfr⟩
  obtain ⟨s', hw'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := w) z (hsh ▸ hY)
    (by omega)
  refine ⟨_, (exec_seq_instr_litIdx I (dst := ⟨Y, .var w⟩) (e := 0) hz hw').trans
    (exec_skip I _), (Store.shape_of_write_eq_some hw').trans hsh, hps, fun j hj => ?_,
    fun q b i hb => (Store.read_of_write_eq_some_of_ne hw' (Or.inl hb)).trans (hfr q b i hb)⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact (Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega))).trans (hY' j hj)
  · exact Store.read_of_write_eq_some hw'

set_option maxHeartbeats 3200000 in
-- The initialisation runs eleven instructions, a loop and a copy kernel before the tail.
/-- EP2: after the allocations, the run of `NLAlib.eighProg` succeeds: the initialisation writes
the constants, the sizes ($n$ at slot $0$ and $0$ elsewhere), $\mathbf{A}$, $R_0$ and
$\varepsilon$ at depth $0$, which are the hypotheses of `ep2_tail`. -/
private theorem ep2_body {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (hℓ : 1 ≤ ℓ₀)
    {A par U dv c Ma Ua Qa Ea Sz Kd Kp Lv Su Sg : ℕ} {σ : St P K C}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hMa : Ma = c + 1) (hUa : Ua = c + 2) (hQa : Qa = c + 3) (hEa : Ea = c + 4) (hSz : Sz = c + 5)
    (hKd : Kd = c + 6) (hKp : Kp = c + 7) (hLv : Lv = c + 8) (hSu : Su = c + 9)
    (hSg : Sg = c + 10) (hlt : ∀ j ∈ [A, par, U, dv], j < c)
    (hsc : σ.store.shape[c]? = some (p, 5))
    (hsMa : σ.store.shape[Ma]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)))
    (hsUa : σ.store.shape[Ua]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)))
    (hsQa : σ.store.shape[Qa]? = some (p, 2 * (n * n) * (ℓ₀ + 1)))
    (hsEa : σ.store.shape[Ea]? = some (p, n * (ℓ₀ + 1 + 1)))
    (hsSz : σ.store.shape[Sz]? = some (p, n * (ℓ₀ + 1 + 1) + 1))
    (hsKd : σ.store.shape[Kd]? = some (p, n * (ℓ₀ + 1)))
    (hsKp : σ.store.shape[Kp]? = some (p, n * (ℓ₀ + 1)))
    (hsLv : σ.store.shape[Lv]? = some (p, 2 * (ℓ₀ + 1 + 1)))
    (hsSu : σ.store.shape[Su]? = some (p, n)) (hsSg : σ.store.shape[Sg]? = some (p, 4 * (n * n)))
    (hA : pairLayout.Holds σ.store p A 0 A₀)
    (hpar : σ.store.read p par 0 = some R₀ ∧ σ.store.read p par 1 = some ε ∧
      σ.store.read p par 2 = some β)
    (hU : ∃ len, σ.store.shape[U]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hdv : ∃ len, σ.store.shape[dv]? = some (p, len) ∧ n ≤ len)
    (hpos : σ.pos .uniform = 0 ∧ σ.pos .gaussian = 0) :
    ∃ st', exec I (Builder.run (ι := ι) (do
      ins (.lit p ⟨c, 0⟩ 1)
      ins (.litIdx p ⟨c, 1⟩ 2)
      ins (.bin p .div ⟨c, 2⟩ ⟨c, 0⟩ ⟨c, 1⟩)
      ins (.un p .neg ⟨c, 3⟩ ⟨c, 0⟩)
      ins (.un p .sqrt ⟨c, 4⟩ ⟨c, 2⟩)
      forRange (IExp.const n * (IExp.const ℓ₀ + 1 + 1) + 1) fun w =>
        ins (.litIdx p ⟨Sz, .var w⟩ 0)
      ins (.litIdx p ⟨Sz, 0⟩ (.const n))
      zcopy p (.const n) (.const n) A 0 Ma 0
      ins (.copy p ⟨Lv, 0⟩ ⟨par, 0⟩)
      ins (.copy p ⟨Lv, 1⟩ ⟨par, 1⟩)
      forRange (IExp.const ℓ₀ + 1) fun d =>
        eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv Su Sg Ma Ua Qa Ea
          Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
      eighBottomLevel p (.const n) (IExp.const ℓ₀ + 1) Ua Ea Sz
      forRange (IExp.const ℓ₀ + 1) fun d' =>
        eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩
      zcopy p (.const n) (.const n) Ua 0 U 0
      forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨Ea, .var i⟩))) σ = some st' := by
  subst hMa hUa hQa hEa hSz hKd hKp hLv hSu hSg
  have lA : A < c := hlt A (by simp)
  have lpar : par < c := hlt par (by simp)
  have lU : U < c := hlt U (by simp)
  have ldv : dv < c := hlt dv (by simp)
  -- the values of the constants
  obtain ⟨o, ho, ho1⟩ := hlit p 1 (by omega)
  have ho' : I.sem.lit p 1 = some o := by simpa using ho
  obtain ⟨tw, htw, htw2⟩ := hlit p 2 (by omega)
  obtain ⟨hf, hfh, δ, hδ, hfd⟩ := el2_bin hsem p (b := .div) trivial (x := o) (y := tw)
    (fun _ => by rw [htw2]; norm_num)
  obtain ⟨ng, hng, -⟩ := hsem.neg p o
  have hf0 : 0 ≤ dec p hf := by
    rw [hfd, ho1, htw2]
    have := (abs_le.mp hδ).1
    simp only [BinOp.realOp]
    apply mul_nonneg (by positivity)
    linarith
  obtain ⟨sq, hsq⟩ := hsem.sqrt_ok p hf hf0
  obtain ⟨z0, hz0, -⟩ := hlit p 0 (by omega)
  obtain ⟨zn, hzn, -⟩ := hlit p n (by omega)
  -- the constants
  obtain ⟨S1, w1⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) o hsc (by norm_num)
  have sh1 := Store.shape_of_write_eq_some w1
  obtain ⟨S2, w2⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) tw
    (by rw [sh1]; exact hsc) (by norm_num)
  have sh2 := (Store.shape_of_write_eq_some w2).trans sh1
  obtain ⟨S3, w3⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2) hf
    (by rw [sh2]; exact hsc) (by norm_num)
  have sh3 := (Store.shape_of_write_eq_some w3).trans sh2
  obtain ⟨S4, w4⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 3) ng
    (by rw [sh3]; exact hsc) (by norm_num)
  have sh4 := (Store.shape_of_write_eq_some w4).trans sh3
  obtain ⟨S5, w5⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 4) sq
    (by rw [sh4]; exact hsc) (by norm_num)
  have sh5 := (Store.shape_of_write_eq_some w5).trans sh4
  have r20 : S2.read p c 0 = some o :=
    (Store.read_of_write_eq_some_of_ne w2 (Or.inr (by omega))).trans
      (Store.read_of_write_eq_some w1)
  have r30 : S3.read p c 0 = some o :=
    (Store.read_of_write_eq_some_of_ne w3 (Or.inr (by omega))).trans r20
  have r21 : S2.read p c 1 = some tw := Store.read_of_write_eq_some w2
  have r42 : S4.read p c 2 = some hf :=
    (Store.read_of_write_eq_some_of_ne w4 (Or.inr (by omega))).trans
      (Store.read_of_write_eq_some w3)
  have fr5 : ∀ q b i, b ≠ c → S5.read q b i = σ.store.read q b i := fun q b i hb => by
    rw [Store.read_of_write_eq_some_of_ne w5 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne w4 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne w3 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne w2 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne w1 (Or.inl hb)]
  have c5 : S5.read p c 0 = some o ∧ S5.read p c 1 = some tw ∧ S5.read p c 2 = some hf ∧
      S5.read p c 3 = some ng ∧ S5.read p c 4 = some sq := by
    refine ⟨?_, ?_, ?_, ?_, Store.read_of_write_eq_some w5⟩
    · rw [Store.read_of_write_eq_some_of_ne w5 (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne w4 (Or.inr (by omega)), r30]
    · rw [Store.read_of_write_eq_some_of_ne w5 (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne w4 (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne w3 (Or.inr (by omega)), r21]
    · rw [Store.read_of_write_eq_some_of_ne w5 (Or.inr (by omega)), r42]
    · rw [Store.read_of_write_eq_some_of_ne w5 (Or.inr (by omega)), Store.read_of_write_eq_some w4]
  refine ep2_ex_lit (by exact ho') (by exact w1) ?_
  refine el2_ex_litIdx (by exact htw) (by exact w2) ?_
  refine el2_ex_bin (by exact r20) (by exact r21) hfh (by exact w3) ?_
  refine ep2_ex_un (by exact r30) hng (by exact w4) ?_
  refine ep2_ex_un (by exact r42) hsq (by exact w5) ?_
  refine el2_name fun σ5 hσ5 => ?_
  have h5s : σ5.store = S5 := by rw [hσ5]
  have h5p : σ5.pos = σ.pos := by rw [hσ5]
  -- the sizes
  obtain ⟨σ6, h6, sh6, p6, r6, fr6⟩ := ep2_lits (ι := ι) (st := σ5)
    (m := IExp.const n * (IExp.const ℓ₀ + 1 + 1) + 1) (by exact hz0)
    (by rw [h5s, sh5]; exact hsSz) le_rfl
  refine ep2_ex_bind (by exact (exec_seq_skip I _ _).trans h6) ?_ (by intro _; rfl)
  obtain ⟨S7, w7⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) zn
    (by rw [sh6, h5s, sh5]; exact hsSz) (by positivity)
  refine el2_ex_litIdx (by exact hzn) (by exact w7) ?_
  refine el2_name fun σ7 hσ7 => ?_
  have h7s : σ7.store = S7 := by rw [hσ7]
  have h7p : σ7.pos = σ.pos := by rw [hσ7]; exact p6.trans h5p
  have sh7 : σ7.store.shape = σ.store.shape := by
    rw [h7s, Store.shape_of_write_eq_some w7, sh6, h5s, sh5]
  have fr7 : ∀ q b i, b ≠ c → b ≠ c + 5 → σ7.store.read q b i = σ.store.read q b i :=
    fun q b i h1 h2 => by
      rw [h7s, Store.read_of_write_eq_some_of_ne w7 (Or.inl h2), fr6 q b i h2, h5s, fr5 q b i h1]
  -- the root's matrix
  have hA7 : pairLayout.Holds σ7.store p A 0 A₀ :=
    hA.of_forall_read_eq fun i _ _ => fr7 _ _ _ (by omega) (by omega)
  have hMa7 : σ7.store.shape[c + 1]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)) := by
    rw [sh7]; exact hsMa
  obtain ⟨σ8, h8⟩ := exists_exec_zcopy (ι := ι) p n n (X := A) (xo := 0) (Y := c + 1) (yo := 0)
    hA7 (el1_bd_ne (by omega)) ⟨_, hMa7, by
      change 0 + 2 * (n * n) ≤ 2 * (n * n) * (ℓ₀ + 1 + 1)
      nlinarith⟩
  obtain ⟨HMa, F8, S8, P8⟩ := holds_of_exec_zcopy p n n hA7 (el1_bd_ne (by omega)) h8
  refine ep2_ex_bind (by exact h8) ?_ (by intro _; rfl)
  have fr8 : ∀ q b i, b ≠ c → b ≠ c + 5 → b ≠ c + 1 → σ8.store.read q b i = σ.store.read q b i :=
    fun q b i h1 h2 h3 => (F8 q b i (el1_bd_ne h3)).trans (fr7 q b i h1 h2)
  -- the window and tolerance of the root
  obtain ⟨S9, w9⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) R₀
    (by rw [S8, sh7]; exact hsLv) (by omega)
  refine ep2_ex_copy (by exact (fr8 p par 0 (by omega) (by omega) (by omega)).trans hpar.1)
    (by exact w9) ?_
  obtain ⟨S10, w10⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) ε
    (by rw [Store.shape_of_write_eq_some w9, S8, sh7]; exact hsLv) (by omega)
  have r9 : S9.read p par 1 = some ε :=
    (Store.read_of_write_eq_some_of_ne w9 (Or.inl (by omega))).trans
      ((fr8 p par 1 (by omega) (by omega) (by omega)).trans hpar.2.1)
  refine ep2_ex_copy (by exact r9) (by exact w10) ?_
  refine el2_name fun σ10 hσ10 => ?_
  have h10s : σ10.store = S10 := by rw [hσ10]
  have sh10 : σ10.store.shape = σ.store.shape := by
    rw [h10s, Store.shape_of_write_eq_some w10, Store.shape_of_write_eq_some w9, S8, sh7]
  have fr10 : ∀ q b i, b ≠ c + 8 → σ10.store.read q b i = σ8.store.read q b i :=
    fun q b i h => by
      rw [h10s, Store.read_of_write_eq_some_of_ne w10 (Or.inl h),
        Store.read_of_write_eq_some_of_ne w9 (Or.inl h)]
  have frσ : ∀ q b i, b ≠ c → b ≠ c + 5 → b ≠ c + 1 → b ≠ c + 8 →
      σ10.store.read q b i = σ.store.read q b i :=
    fun q b i h1 h2 h3 h4 => (fr10 q b i h4).trans (fr8 q b i h1 h2 h3)
  have hSz10 : ∀ i, σ10.store.read p (c + 5) i = σ7.store.read p (c + 5) i := fun i =>
    (fr10 p _ i (by omega)).trans (F8 p _ i (el1_bd_ne (by omega)))
  have hSz0 : σ10.store.read p (c + 5) 0 = some zn := (hSz10 0).trans (by
    rw [h7s]; exact Store.read_of_write_eq_some w7)
  have hSzj : ∀ j, j ≠ 0 → j < n * (ℓ₀ + 1 + 1) + 1 → σ10.store.read p (c + 5) j = some z0 :=
    fun j hj0 hj => (hSz10 j).trans (by
      rw [h7s, Store.read_of_write_eq_some_of_ne w7 (Or.inr hj0)]
      exact r6 j hj)
  let H : EighArenas := ⟨c + 1, c + 2, c + 3, c + 4, c + 5, c + 6, c + 7, c + 8⟩
  have hc10 : σ10.store.read p c 0 = some o ∧ σ10.store.read p c 1 = some tw ∧
      σ10.store.read p c 2 = some hf ∧ σ10.store.read p c 3 = some ng ∧
      σ10.store.read p c 4 = some sq := by
    have e : ∀ i, σ10.store.read p c i = S5.read p c i := fun i => by
      rw [fr10 p c i (by omega), F8 p c i (el1_bd_ne (by omega)), h7s,
        Store.read_of_write_eq_some_of_ne w7 (Or.inl (by omega)), fr6 p c i (by omega), h5s]
    rw [e, e, e, e, e]
    exact c5
  refine ep2_tail hmm hqr hsem p hu n ℓ₀ F hlit htn hℓ H (par := par) (Su := c + 9) (Sg := c + 10)
    (c := c) (U := U) (dv := dv) (A₀ := A₀) (σ := σ10) (R₀ := R₀) (ε := ε) (β := β) hε hR₀
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨by simp [H, EighArenas.handles], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [sh10] <;> assumption
  · simp [H, EighArenas.handles]; omega
  · simp [H, EighArenas.handles]; omega
  · simp [H, EighArenas.handles]; omega
  · -- the root at depth 0
    refine ⟨fun a lo y ha hay => ?_, fun lo hlo hno => ?_, ?_, ?_⟩
    · rw [List.length_eq_zero_iff.mp ha] at hay
      cases hay
      refine ⟨el1_readsIdx hlit htn (k := n) (by omega) ?_, ?_⟩
      · simp only [Nat.mul_zero, Nat.add_zero]
        rw [hSz0]; exact hzn.symm
      · simp only [Nat.mul_zero, Nat.add_zero]
        exact HMa.of_forall_read_eq fun i _ _ => fr10 p _ i (by omega)
    · have hlo0 : lo ≠ 0 := by
        rintro rfl
        exact hno [] _ rfl rfl
      refine el1_readsIdx hlit htn (k := 0) (by omega) ?_
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [hSzj lo hlo0 (by nlinarith)]
      exact hz0.symm
    · change σ10.store.read p (c + 8) 0 = some R₀
      rw [h10s, Store.read_of_write_eq_some_of_ne w10 (Or.inr (by omega))]
      exact Store.read_of_write_eq_some w9
    · change σ10.store.read p (c + 8) 1 = some ε
      rw [h10s]
      exact Store.read_of_write_eq_some w10
  · intro j hj1 hj2
    by_cases hj0 : j = 0
    · subst hj0
      have hn0 : n = 0 := by omega
      have := el1_readsIdx hlit htn (k := n) (s := σ10.store) (p := p) (b := c + 5) (i := 0)
        (by omega) (by rw [hSz0]; exact hzn.symm)
      rwa [hn0] at this
    · exact el1_readsIdx hlit htn (k := 0) (by omega)
        (by rw [hSzj j hj0 (by omega)]; exact hz0.symm)
  · rw [hσ10]; exact (P8.trans h7p) ▸ hpos
  · exact ⟨(frσ p par 0 (by omega) (by omega) (by omega) (by omega)).trans hpar.1,
      (frσ p par 2 (by omega) (by omega) (by omega) (by omega)).trans hpar.2.2⟩
  · exact ⟨n, by rw [sh10]; exact hsSu, le_rfl⟩
  · exact ⟨4 * (n * n), by rw [sh10]; exact hsSg, le_rfl⟩
  · refine ⟨by rw [hc10.1]; exact ho'.symm, by rw [hc10.2.1]; exact htw.symm, ?_, ?_, ?_⟩
    · rw [hc10.2.2.1]
      change some hf = some ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)
      rw [ho', htw]
      simp [hfh]
    · rw [hc10.2.2.2.1]
      change some ng = some ((I.sem.un p .neg ((I.sem.lit p 1).getD default)).getD default)
      rw [ho']
      simp [hng]
    · rw [hc10.2.2.2.2]
      change some sq = some ((I.sem.un p .sqrt ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)).getD default)
      rw [ho', htw]
      simp [hfh, hsq]
  · rw [sh10]; exact hU
  · rw [sh10]; exact hdv

omit [DecidableEq P] [Inhabited K] in
/-- EP2: the shape of a pushed store below or above its top. -/
private theorem ep2_sh {s : Store P K} {b : ℕ} (x : P × Array (Option K)) (hb : b ≠ s.size) :
    (Store.shape (s.push x))[b]? = s.shape[b]? := by
  simp [Store.shape, Array.getElem?_push, hb]

/-- **The refinement of the spectral bisection program, success**: under the standard model at $u$
with every value in range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor
conversion, if the kernels `mm`, `qr` of `I` are routines on interleaved pairs, $\ell_0 \ge 1$,
$\varepsilon$ and $R_0$ decode to nonnegative values, and the buffers `U`, `dv` at tag `p` have
$2n^2$ and $n$ cells (hypotheses on the inputs and the tape positions at $0$ as
`NLAlib.holds_of_exec_eighProg`), then every run of `NLAlib.eighProg` succeeds. No printed source.
Proof: the allocations succeed; the initialisation (`lit_ok`, copies of initialised cells, the
pilot's `NLAlib.Computation.exists_exec_zcopy`); the downward loop by
`NLAlib.Computation.exists_exec_loop_eq_some_of_forall` with `NLAlib.exists_exec_eighDownLevel` and
the invariant `NLAlib.holds_of_exec_eighDownLevel` gives; `NLAlib.exists_exec_eighBottomLevel`; the
upward loop with `NLAlib.exists_exec_eighUpLevel`; the final copies and the pops. L, about 100
lines. `NLAlib.exists_exec_eighDownLevel` at level $d$ needs the exact constants `hc` (cell $2$ of
`c` is $\mathrm{fl}(1/\mathrm{fl}(2))$ of the machine, a division of the literals $1$ and $2$; cell
$3$ is $-1$; cell $4$ is `NLAlib.Computation.ScalarSem.sqrtHalf`, the square root of cell $2$) and
the tape positions `hpos` ($nd$ uniform, $4n^2 d$ Gaussian after $d$ levels, by the position
advance of `NLAlib.holds_of_exec_eighDownLevel`). -/
theorem exists_exec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (hℓ : 1 ≤ ℓ₀) {A par U dv : ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hbufs : [A, par, U, dv].Nodup) (hsize : ∀ j ∈ [A, par, U, dv], j < st.store.size)
    (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0)
    (hU : ∃ len, st.store.shape[U]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hdv : ∃ len, st.store.shape[dv]? = some (p, len) ∧ n ≤ len) :
    ∃ st', exec I (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run st =
      some st' := by
  have lA := hsize A (by simp)
  have lpar := hsize par (by simp)
  have lU := hsize U (by simp)
  have ldv := hsize dv (by simp)
  change ∃ st', exec I (.seq (.alloc p 5 _) .skip) st = some st'
  rw [exec_seq_skip, exec_alloc]
  refine el2_map_ex ?_
  iterate 10
    change ∃ a, exec I (.alloc p _ _) _ = some a
    rw [exec_alloc]
    refine el2_map_ex ?_
  refine ep2_body hmm hqr hsem p hu n ℓ₀ F hlit htn hℓ (A := A) (par := par) (U := U) (dv := dv)
    (A₀ := A₀) (R₀ := R₀) (ε := ε) (β := β) hε hR₀ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsize
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | (simp only [Array.size_push]; done)
    | (simp (disch := ((try simp only [Array.size_push]); omega)) only [ep2_sh,
        Store.getElem?_shape_push_size]; done)
    | (simp (disch := ((try simp only [Array.size_push]); omega)) only [ep2_sh,
        Store.getElem?_shape_push_size]; rfl)
    | skip
  · exact hA.of_forall_read_eq fun i _ _ => by
      simp (disch := ((try simp only [Array.size_push]); omega)) only [Store.read_push_of_ne]
  · simp (disch := ((try simp only [Array.size_push]); omega)) only [Store.read_push_of_ne]
    exact hpar
  · simp (disch := ((try simp only [Array.size_push]); omega)) only [ep2_sh]
    exact hU
  · simp (disch := ((try simp only [Array.size_push]); omega)) only [ep2_sh]
    exact hdv
  · exact hpos

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- **The registered tree instantiates to the builder**: at the sizes $N$ and $(\ell_0, F)$ the tree
`NLAlib.eighProg.compiled` is `NLAlib.eighProg` on the declared buffers $0$ to $3$. No printed
source.
Proof: `rfl`, the instantiation equation of a compiled family (as the pilot's
`NLAlib.newtonSchulzSignProg.toStmt_compiled`). S, 1 line. -/
theorem eighProg.toStmt_compiled (p : P) (mm qr : ι) (N : ℕ) (n : Fin 2 → ℕ) :
    (eighProg.compiled p mm qr).toStmt N n =
      ProgFamily.inst (r := 2) (b := 4) (fun _ _ N n h =>
        (eighProg p mm qr N (n 0) (n 1) (h 0) (h 1) (h 2) (h 3)).run) N n := by
  -- the unfolding of the four buffers is deeper than the default recursion limit
  set_option maxRecDepth 10000 in rfl

/-- **The registered tree computes `NLAlib.eigh`**: under the hypotheses of
`NLAlib.holds_of_exec_eighProg`, a successful run of `NLAlib.eighProg.compiled` at the sizes $N$ and
$(\ell_0, F)$ from the initial state with the stored $\mathbf{A}$, the stored $R_0$, $\varepsilon$,
$\beta$, and $2N^2$ and $N$ empty cells as declared buffers ends with declared buffers $2$ and $3$
holding `NLAlib.eigh` on the machine of the interpretation with the tree of samples at the slots.
No printed source.
Proof: `NLAlib.Computation.Prog.exec_eq_exec_toStmt`, `NLAlib.eighProg.toStmt_compiled`, then
`NLAlib.holds_of_exec_eighProg` with the pilot's `NLAlib.Computation.EntryLayout.holds_inputState`
and the reads of declared buffer $1$ (`NLAlib.Computation.inputState`, tape positions $0$). S,
about 15 lines. -/
theorem eighProg.holds_of_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (N ℓ₀ F : ℕ) (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (R₀ ε β : K) {st' : St P K C}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some R₀, some ε, some β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none]) = some st') :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M N F R₀ β 0 0 ⟨N, A₀, R₀, ε, ℓ₀⟩)
    pairLayout.Holds st'.store p 2 0 r.1 ∧ ∀ i : Fin N, st'.store.read p 3 i = some (r.2 i) := by
  rw [Prog.exec_eq_exec_toStmt, eighProg.toStmt_compiled] at h
  set bufs : List (Array (Option K)) := [(pairLayout.toArray A₀).map some,
    #[some R₀, some ε, some β], Array.replicate (2 * (N * N)) none, Array.replicate N none]
    with hbufs
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (bufs := bufs) (k := 0) (Y := A₀)
    rfl
  have h' : exec I (eighProg p mm qr (.const N) (.const ℓ₀) (.const F) 0 1 2 3).run
      (inputState p bufs) = some st' := h
  exact holds_of_exec_eighProg hmm hqr p hflag hcmp N ℓ₀ F hlit htn (by simp)
    (by simp [inputState, bufs, Store.shape]) hA (by simp [inputState, bufs, Store.read])
    (by simp [inputState]) h'

/-- **The registered tree succeeds** under the hypotheses of `NLAlib.exists_exec_eighProg`, from the
initial state of `NLAlib.eighProg.holds_of_exec_compiled`. No printed source.
Proof: as `NLAlib.eighProg.holds_of_exec_compiled`, with `NLAlib.exists_exec_eighProg`; declared
buffers $2$ and $3$ have $2N^2$ and $N$ cells at tag `p` (`NLAlib.Computation.inputState`,
`Array.size_replicate`). S, about 15 lines. -/
theorem eighProg.exists_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (N ℓ₀ F : ℕ)
    (hℓ : 1 ≤ ℓ₀) (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (R₀ ε β : K) (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀) :
    ∃ st' : St P K C, (eighProg.compiled p mm qr).exec I N ![ℓ₀, F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some R₀, some ε, some β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none]) = some st' := by
  rw [Prog.exec_eq_exec_toStmt, eighProg.toStmt_compiled]
  set bufs : List (Array (Option K)) := [(pairLayout.toArray A₀).map some,
    #[some R₀, some ε, some β], Array.replicate (2 * (N * N)) none, Array.replicate N none]
    with hbufs
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (bufs := bufs) (k := 0) (Y := A₀)
    rfl
  exact exists_exec_eighProg hmm hqr hsem p hu N ℓ₀ F hlit htn hℓ (A := 0) (par := 1) (U := 2)
    (dv := 3) (st := inputState p bufs) (A₀ := A₀) (R₀ := R₀) (ε := ε) (β := β) hε hR₀
    (by simp) (by simp [inputState, bufs, Store.shape]) hA (by simp [inputState, bufs, Store.read])
    (by simp [inputState]) ⟨2 * (N * N), by simp [inputState, Store.getElem?_shape, bufs], by simp⟩
    ⟨N, by simp [inputState, Store.getElem?_shape, bufs], by simp⟩

/-! ### EP6 helpers -/

/-- Polynomials in $(N, \ell_0, F)$ with natural coefficients, as unnormalized lists of terms
(coefficient, exponents). -/
private abbrev ep6_Poly := List (ℕ × ℕ × ℕ × ℕ)

/-- The value of a polynomial. -/
private def ep6_ev (N L F : ℕ) (p : ep6_Poly) : ℕ :=
  (p.map fun e => e.1 * (N ^ e.2.1 * L ^ e.2.2.1 * F ^ e.2.2.2)).sum

/-- The product of two polynomials. -/
private def ep6_pmul (p q : ep6_Poly) : ep6_Poly :=
  p.flatMap fun a => q.map fun b => (a.1 * b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

private theorem ep6_ev_append (N L F : ℕ) (p q : ep6_Poly) :
    ep6_ev N L F (p ++ q) = ep6_ev N L F p + ep6_ev N L F q := by
  simp [ep6_ev]

private theorem ep6_ev_pmul (N L F : ℕ) (p q : ep6_Poly) :
    ep6_ev N L F (ep6_pmul p q) = ep6_ev N L F p * ep6_ev N L F q := by
  induction p with
  | nil => simp [ep6_pmul, ep6_ev]
  | cons a p ih =>
    have ih' : ep6_ev N L F (p.flatMap fun a => q.map fun b =>
        (a.1 * b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)) =
        ep6_ev N L F p * ep6_ev N L F q := ih
    simp only [ep6_pmul, List.flatMap_cons, ep6_ev_append, ih']
    simp only [ep6_ev, List.map_cons, List.sum_cons, List.map_map, add_mul]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro b _
    simp only [Function.comp, pow_add]
    ring

/-- An upper bound of an index expression by a polynomial: truncated subtraction and the
remainder by their first argument. -/
private def ep6_up {ni : ℕ} (σ : Fin ni → ep6_Poly) : IExp (Fin ni) → ep6_Poly
  | .var v => σ v
  | .const n => [(n, 0, 0, 0)]
  | .add a b => ep6_up σ a ++ ep6_up σ b
  | .sub a _ => ep6_up σ a
  | .mul a b => ep6_pmul (ep6_up σ a) (ep6_up σ b)
  | .mod a _ => ep6_up σ a

private theorem ep6_evalIn_le_up {N L F ni : ℕ} {ρ : Fin ni → ℕ} {σ : Fin ni → ep6_Poly}
    (h : ∀ v, ρ v ≤ ep6_ev N L F (σ v)) :
    ∀ e : IExp (Fin ni), e.evalIn ρ ≤ ep6_ev N L F (ep6_up σ e)
  | .var v => h v
  | .const n => by simp [ep6_up, ep6_ev, IExp.evalIn]
  | .add a b => by
    simp only [IExp.evalIn, ep6_up, ep6_ev_append]
    exact Nat.add_le_add (ep6_evalIn_le_up h a) (ep6_evalIn_le_up h b)
  | .sub a _ => (Nat.sub_le _ _).trans (ep6_evalIn_le_up h a)
  | .mul a b => by
    simp only [IExp.evalIn, ep6_up, ep6_ev_pmul]
    exact Nat.mul_le_mul (ep6_evalIn_le_up h a) (ep6_evalIn_le_up h b)
  | .mod a _ => (Nat.mod_le _ _).trans (ep6_evalIn_le_up h a)

/-- Extension of a polynomial environment by a last entry. -/
private def ep6_snoc {n : ℕ} (σ : Fin n → ep6_Poly) (x : ep6_Poly) : Fin (n + 1) → ep6_Poly :=
  fun i => if h : (i : ℕ) < n then σ ⟨i, h⟩ else x

private theorem ep6_snoc_le {N L F n : ℕ} {ρ : Fin n → ℕ} {σ : Fin n → ep6_Poly}
    (h : ∀ v, ρ v ≤ ep6_ev N L F (σ v)) {i : ℕ} {x : ep6_Poly} (hi : i ≤ ep6_ev N L F x) :
    ∀ v, Fin.snoc (α := fun _ => ℕ) ρ i v ≤ ep6_ev N L F (ep6_snoc σ x v) := by
  intro v
  by_cases hv : (v : ℕ) < n
  · simp only [Fin.snoc, hv, dif_pos, ep6_snoc, cast_eq]
    exact h _
  · simp only [Fin.snoc, hv, dif_neg, not_false_eq_true, ep6_snoc, cast_eq]
    exact hi

/-- A class of operation kinds, forgetting tags, oracle names and dimensions. -/
private def ep6_cls {P ι : Type} : OpKind P ι → ℕ
  | .bin _ b => match b with
    | .add => 10 | .sub => 11 | .mul => 12 | .div => 13 | _ => 14
  | .un _ u => match u with
    | .neg => 20 | .sqrt => 23 | _ => 21
  | .lit _ => 1
  | .cmp _ => 6
  | .copy _ => 2
  | .draw _ d => match d with
    | .gaussian => 30 | .uniform => 32 | _ => 31
  | .convert _ _ => 3
  | .rom _ => 5
  | .load _ _ => 4
  | .matvec _ _ => 8
  | .kcall _ _ _ => 9
  | .toNat _ => 7

/-- The tag of an operation kind. -/
private def ep6_ktag {P ι : Type} : OpKind P ι → P
  | .bin p _ => p | .un p _ => p | .lit p => p | .cmp p => p | .copy p => p | .draw p _ => p
  | .convert p _ => p | .rom p => p | .load p _ => p | .matvec p _ => p | .kcall p _ _ => p
  | .toNat p => p

/-- The constant polynomial $1$ if the classes agree, $0$ otherwise. -/
private def ep6_ind (c d : ℕ) : ep6_Poly := if d = c then [(1, 0, 0, 0)] else []

private theorem ep6_ev_ind (N L F c d : ℕ) :
    ep6_ev N L F (ep6_ind c d) = if d = c then 1 else 0 := by
  unfold ep6_ind; split_ifs <;> simp [ep6_ev]

/-- **A crude count of the operations of class `c`**: loops by their trip-count bound times the
body at the largest index, index binders by the body at the bound, branches by their sum. -/
private def ep6_C {P ι : Type} (c : ℕ) :
    {nb ni : ℕ} → FStmt P ι nb ni → (Fin ni → ep6_Poly) → ep6_Poly
  | _, _, .skip, _ => []
  | _, _, .seq s t, σ => ep6_C c s σ ++ ep6_C c t σ
  | _, _, .instr i, _ =>
      ep6_ind c (ep6_cls ((i.subst (fun _ => 0) (fun _ => .const 0)).kind (ι := ι)))
  | _, _, .apply _ _ _ _ _ _ cols, σ => ep6_ind c 4 ++ ep6_pmul (ep6_up σ cols) (ep6_ind c 8)
  | _, _, .rom _ _ _, _ => ep6_ind c 5
  | _, _, .alloc _ _ b, σ => ep6_C c b σ
  | _, _, .loop n b, σ => ep6_pmul (ep6_up σ n) (ep6_C c b (ep6_snoc σ (ep6_up σ n)))
  | _, _, .whileFuel f _ _ _ _ b, σ => ep6_pmul (ep6_up σ f) (ep6_ind c 6 ++ ep6_C c b σ)
  | _, _, .ite _ _ _ _ t e, σ => ep6_ind c 6 ++ (ep6_C c t σ ++ ep6_C c e σ)
  | _, _, .named _ _ b, σ => ep6_C c b σ
  | _, _, .kcall _ _ _ _ _, _ => ep6_ind c 9
  | _, _, .bindIdx _ _ bd b, σ => ep6_ind c 7 ++ ep6_C c b (ep6_snoc σ (ep6_up σ bd))

/-- A crude bound on the additional live cells (sums for maxima). -/
private def ep6_Cc {P ι : Type} : {nb ni : ℕ} → FStmt P ι nb ni → (Fin ni → ep6_Poly) → ep6_Poly
  | _, _, .seq s t, σ => ep6_Cc s σ ++ ep6_Cc t σ
  | _, _, .alloc _ len b, σ => ep6_up σ len ++ ep6_Cc b σ
  | _, _, .loop n b, σ => ep6_Cc b (ep6_snoc σ (ep6_up σ n))
  | _, _, .whileFuel _ _ _ _ _ b, σ => ep6_Cc b σ
  | _, _, .ite _ _ _ _ t e, σ => ep6_Cc t σ ++ ep6_Cc e σ
  | _, _, .named _ _ b, σ => ep6_Cc b σ
  | _, _, .bindIdx _ _ bd b, σ => ep6_Cc b (ep6_snoc σ (ep6_up σ bd))
  | _, _, _, _ => []

/-- The tags of a tree. -/
private def ep6_tags {P ι : Type} : {nb ni : ℕ} → FStmt P ι nb ni → List P
  | _, _, .skip => []
  | _, _, .seq s t => ep6_tags s ++ ep6_tags t
  | _, _, .instr i => [ep6_ktag ((i.subst (fun _ => 0) (fun _ => .const 0)).kind (ι := ι))]
  | _, _, .apply _ p _ _ _ _ _ => [p]
  | _, _, .rom p _ _ => [p]
  | _, _, .alloc p _ b => p :: ep6_tags b
  | _, _, .loop _ b => ep6_tags b
  | _, _, .whileFuel _ p _ _ _ b => p :: ep6_tags b
  | _, _, .ite p _ _ _ t e => p :: (ep6_tags t ++ ep6_tags e)
  | _, _, .named _ _ b => ep6_tags b
  | _, _, .kcall _ p _ _ _ => [p]
  | _, _, .bindIdx p _ _ b => p :: ep6_tags b


private theorem ep6_sum_le {α : Type} [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (l : List ℕ) (f : ℕ → α) (B : α) (h : ∀ i ∈ l, f i ≤ B) :
    (l.map f).sum ≤ l.length • B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, succ_nsmul']
    exact add_le_add (h a List.mem_cons_self) (ih fun i hi => h i (List.mem_cons_of_mem a hi))

omit [DecidableEq P] in
private theorem ep6_supRange_count_le {f : ℕ → StaticCost P ι} {m B : ℕ} {κ : OpKind P ι}
    (h : ∀ k < m, (f k).count κ ≤ B) : (StaticCost.supRange m f).count κ ≤ B := by
  unfold StaticCost.supRange
  suffices ∀ l : List ℕ, (∀ k ∈ l, k < m) →
      (l.foldr (fun k c => (f k).branch c) StaticCost.zero).count κ ≤ B from
    this _ fun k hk => List.mem_range.mp hk
  intro l hl
  induction l with
  | nil => simp [StaticCost.zero]
  | cons a l ih =>
    simp only [List.foldr_cons, StaticCost.branch, Finsupp.sup_apply]
    exact max_le (h a (hl a List.mem_cons_self)) (ih fun k hk => hl k (List.mem_cons_of_mem a hk))

omit [DecidableEq P] in
private theorem ep6_supRange_cells_le {f : ℕ → StaticCost P ι} {m B : ℕ} {q : P}
    (h : ∀ k < m, (f k).cells q ≤ B) : (StaticCost.supRange m f).cells q ≤ B := by
  unfold StaticCost.supRange
  suffices ∀ l : List ℕ, (∀ k ∈ l, k < m) →
      (l.foldr (fun k c => (f k).branch c) StaticCost.zero).cells q ≤ B from
    this _ fun k hk => List.mem_range.mp hk
  intro l hl
  induction l with
  | nil => simp [StaticCost.zero]
  | cons a l ih =>
    simp only [List.foldr_cons, StaticCost.branch]
    exact max_le (h a (hl a List.mem_cons_self)) (ih fun k hk => hl k (List.mem_cons_of_mem a hk))

omit [DecidableEq P] in
private theorem ep6_single_le (k κ : OpKind P ι) :
    (Finsupp.single k 1 : OpCount P ι) κ ≤ if ep6_cls k = ep6_cls κ then 1 else 0 := by
  classical
  rw [Finsupp.single_apply]
  split_ifs with h1 h2 <;> simp_all

/-- **The crude count bounds the static count** of every kind by its class. -/
private theorem ep6_count_le (w : P → ℕ) (κ : OpKind P ι) (N L F : ℕ) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ) (σ : Fin ni → ep6_Poly),
      (∀ v, ρ v ≤ ep6_ev N L F (σ v)) →
      (s.staticCost (fun k => Finsupp.single k 1) w ρ).count κ ≤
        ep6_ev N L F (ep6_C (ep6_cls κ) s σ) := by
  intro nb ni s
  induction s with
  | skip => intro ρ σ _; simp [FStmt.staticCost, StaticCost.zero]
  | seq s t ihs iht =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, Finsupp.add_apply, ep6_C, ep6_ev_append]
    exact Nat.add_le_add (ihs ρ σ h) (iht ρ σ h)
  | instr i =>
    intro ρ σ _
    simp only [FStmt.staticCost, StaticCost.step, ep6_C, ep6_ev_ind]
    exact ep6_single_le _ _
  | apply o p d dOff s sOff cols =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.step, ep6_C, ep6_ev_append, ep6_ev_pmul, ep6_ev_ind,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Nat.add_le_add (ep6_single_le _ _)
      (Nat.mul_le_mul (ep6_evalIn_le_up h cols) (ep6_single_le _ _))
  | rom p d i =>
    intro ρ σ _
    simp only [FStmt.staticCost, StaticCost.step, ep6_C, ep6_ev_ind]
    exact ep6_single_le _ _
  | alloc p len body ih =>
    intro ρ σ h
    exact ih ρ σ h
  | loop n body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.sequence_count_apply, ep6_C, ep6_ev_pmul]
    have hn := ep6_evalIn_le_up h n
    refine (ep6_sum_le _ _ (ep6_ev N L F (ep6_C (ep6_cls κ) body
      (ep6_snoc σ (ep6_up σ n)))) ?_).trans ?_
    · intro i hi
      exact ih _ _ (ep6_snoc_le h ((List.mem_range.mp hi).le.trans hn))
    · rw [List.length_range, smul_eq_mul]
      exact Nat.mul_le_mul_right _ hn
  | whileFuel fuel p c x y body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, ep6_C, ep6_ev_pmul, ep6_ev_append,
      ep6_ev_ind]
    exact Nat.mul_le_mul (ep6_evalIn_le_up h fuel) (Nat.add_le_add (ep6_single_le _ _) (ih ρ σ h))
  | ite p c x y t e iht ihe =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.branch, StaticCost.seq, StaticCost.step,
      Finsupp.add_apply, Finsupp.sup_apply, ep6_C, ep6_ev_append, ep6_ev_ind]
    exact Nat.add_le_add (ep6_single_le _ _) (max_le ((iht ρ σ h).trans (Nat.le_add_right _ _))
      ((ihe ρ σ h).trans (Nat.le_add_left _ _)))
  | named name args body ih =>
    intro ρ σ h
    exact ih ρ σ h
  | kcall o p dims ins outs =>
    intro ρ σ _
    simp only [FStmt.staticCost, StaticCost.step, ep6_C, ep6_ev_ind]
    exact ep6_single_le _ _
  | bindIdx p x bound body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, Finsupp.add_apply, ep6_C,
      ep6_ev_append, ep6_ev_ind]
    exact Nat.add_le_add (ep6_single_le _ _) (ep6_supRange_count_le fun k hk => ih _ _
      (ep6_snoc_le h ((Nat.lt_succ_iff.mp hk).trans (ep6_evalIn_le_up h bound))))

/-- **The crude cell bound bounds the static workspace.** -/
private theorem ep6_cells_le (charge : OpKind P ι → OpCount P ι) (w : P → ℕ) (q : P)
    (N L F : ℕ) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ) (σ : Fin ni → ep6_Poly),
      (∀ v, ρ v ≤ ep6_ev N L F (σ v)) →
      (s.staticCost charge w ρ).cells q ≤ ep6_ev N L F (ep6_Cc s σ) := by
  intro nb ni s
  induction s with
  | seq s t ihs iht =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, ep6_Cc, ep6_ev_append]
    exact max_le ((ihs ρ σ h).trans (Nat.le_add_right _ _))
      ((iht ρ σ h).trans (Nat.le_add_left _ _))
  | alloc p len body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.alloc, ep6_Cc, ep6_ev_append]
    refine Nat.add_le_add ?_ (ih ρ σ h)
    split_ifs
    · exact ep6_evalIn_le_up h len
    · exact Nat.zero_le _
  | loop n body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, ep6_Cc]
    exact StaticCost.sequence_cells_le _ _ _ _ fun i hi => ih _ _ (ep6_snoc_le h
      ((List.mem_range.mp hi).le.trans (ep6_evalIn_le_up h n)))
  | whileFuel fuel p c x y body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step, ep6_Cc]
    exact max_le (Nat.zero_le _) (ih ρ σ h)
  | ite p c x y t e iht ihe =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, StaticCost.branch, ep6_Cc,
      ep6_ev_append]
    exact max_le (Nat.zero_le _) (max_le ((iht ρ σ h).trans (Nat.le_add_right _ _))
      ((ihe ρ σ h).trans (Nat.le_add_left _ _)))
  | named name args body ih =>
    intro ρ σ h
    exact ih ρ σ h
  | bindIdx p x bound body ih =>
    intro ρ σ h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, ep6_Cc]
    exact max_le (Nat.zero_le _) (ep6_supRange_cells_le fun k hk => ih _ _
      (ep6_snoc_le h ((Nat.lt_succ_iff.mp hk).trans (ep6_evalIn_le_up h bound))))
  | _ => intro ρ σ _; simp [FStmt.staticCost, StaticCost.step, StaticCost.zero]

/-- A kind whose tag is not a tag of the tree is not counted. -/
private theorem ep6_count_tag (w : P → ℕ) (κ : OpKind P ι) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ), ep6_ktag κ ∉ ep6_tags s →
      (s.staticCost (fun k => Finsupp.single k 1) w ρ).count κ ≤ 0 := by
  classical
  have hs : ∀ k : OpKind P ι, ep6_ktag κ ≠ ep6_ktag k →
      (Finsupp.single k 1 : OpCount P ι) κ ≤ 0 := by
    intro k hk
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact hk rfl
  intro nb ni s
  induction s with
  | skip => intro ρ _; simp [FStmt.staticCost, StaticCost.zero]
  | seq s t ihs iht =>
    intro ρ h
    simp only [ep6_tags, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, Finsupp.add_apply]
    exact Nat.add_le_add (ihs ρ h.1) (iht ρ h.2)
  | instr i =>
    intro ρ h
    simp only [ep6_tags, List.mem_singleton] at h
    exact hs _ h
  | apply o p d dOff s sOff cols =>
    intro ρ h
    simp only [ep6_tags, List.mem_singleton] at h
    simp only [FStmt.staticCost, StaticCost.step, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
    rw [Nat.le_zero.mp (hs (.load p o) h), Nat.le_zero.mp (hs (.matvec p o) h)]
    simp
  | rom p d i =>
    intro ρ h
    simp only [ep6_tags, List.mem_singleton] at h
    exact hs _ h
  | alloc p len body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    exact ih ρ h.2
  | loop n body ih =>
    intro ρ h
    simp only [ep6_tags] at h
    simp only [FStmt.staticCost, StaticCost.sequence_count_apply]
    refine (ep6_sum_le _ _ 0 fun i _ => ih _ h).trans ?_
    simp
  | whileFuel fuel p c x y body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]
    have h1 := hs (.cmp p) h.1
    have h2 := ih ρ h.2
    simp_all
  | ite p c x y t e iht ihe =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.branch, StaticCost.seq, StaticCost.step,
      Finsupp.add_apply, Finsupp.sup_apply]
    have h1 := hs (.cmp p) h.1
    have h2 := iht ρ h.2.1
    have h3 := ihe ρ h.2.2
    omega
  | named name args body ih =>
    intro ρ h
    exact ih ρ h
  | kcall o p dims ins outs =>
    intro ρ h
    simp only [ep6_tags, List.mem_singleton] at h
    exact hs _ h
  | bindIdx p x bound body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, Finsupp.add_apply]
    exact Nat.add_le_add (hs (.toNat p) h.1) (ep6_supRange_count_le fun k _ => ih _ h.2)

/-- A tag that is not a tag of the tree has no workspace. -/
private theorem ep6_cells_tag (charge : OpKind P ι → OpCount P ι) (w : P → ℕ) (q : P) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ), q ∉ ep6_tags s →
      (s.staticCost charge w ρ).cells q ≤ 0 := by
  intro nb ni s
  induction s with
  | seq s t ihs iht =>
    intro ρ h
    simp only [ep6_tags, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq]
    exact max_le (ihs ρ h.1) (iht ρ h.2)
  | alloc p len body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.alloc, if_neg h.1, zero_add]
    exact ih ρ h.2
  | loop n body ih =>
    intro ρ h
    simp only [ep6_tags] at h
    simp only [FStmt.staticCost]
    exact StaticCost.sequence_cells_le _ _ _ _ fun i _ => ih _ h
  | whileFuel fuel p c x y body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step]
    exact max_le (Nat.zero_le _) (ih ρ h.2)
  | ite p c x y t e iht ihe =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, List.mem_append, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, StaticCost.branch]
    exact max_le (Nat.zero_le _) (max_le (iht ρ h.2.1) (ihe ρ h.2.2))
  | named name args body ih =>
    intro ρ h
    exact ih ρ h
  | bindIdx p x bound body ih =>
    intro ρ h
    simp only [ep6_tags, List.mem_cons, not_or] at h
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step]
    exact max_le (Nat.zero_le _) (ep6_supRange_cells_le fun k _ => ih _ h.2)
  | _ => intro ρ _; simp [FStmt.staticCost, StaticCost.step, StaticCost.zero]

/-- The polynomial environment of the sizes $(N, \ell_0, F)$. -/
private def ep6_σ0 : Fin 3 → ep6_Poly :=
  fun v =>
    if v.val = 0 then [(1, 1, 0, 0)] else if v.val = 1 then [(1, 0, 1, 0)] else [(1, 0, 0, 1)]

/-- The check of a scalar class: degrees at most $(3, 1, 1)$ and coefficients summing to at most
$1024$. -/
private def ep6_okS (p : ep6_Poly) : Bool :=
  p.all (fun e => e.2.1 ≤ 3 && e.2.2.1 ≤ 1 && e.2.2.2 ≤ 1) && decide ((p.map (·.1)).sum ≤ 1024)

/-- The check of the workspace: degrees at most $(2, 1, 0)$, coefficients of the terms without
$\ell_0$ summing to at most $192$, with $\ell_0$ to at most $64$. -/
private def ep6_okC (p : ep6_Poly) : Bool :=
  p.all (fun e => e.2.1 ≤ 2 && e.2.2.1 ≤ 1 && e.2.2.2 = 0) &&
    decide ((p.map fun e => if e.2.2.1 = 0 then e.1 else 0).sum ≤ 192) &&
    decide ((p.map fun e => if e.2.2.1 = 0 then 0 else e.1).sum ≤ 64)

private def ep6_mI {P P' VB VI : Type} (f : P → P') : Instr P VB VI → Instr P' VB VI
  | .lit p d q => .lit (f p) d q
  | .litIdx p d e => .litIdx (f p) d e
  | .bin p b d x y => .bin (f p) b d x y
  | .un p u d x => .un (f p) u d x
  | .copy p d s => .copy (f p) d s
  | .draw p dist d => .draw (f p) dist d
  | .convert p q d s => .convert (f p) (f q) d s

/-- A tree with its tags and oracle names renamed. -/
private def ep6_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    {nb ni : ℕ} → FStmt P ι nb ni → FStmt P' ι' nb ni
  | _, _, .skip => .skip
  | _, _, .seq s t => .seq (ep6_map f g s) (ep6_map f g t)
  | _, _, .instr i => .instr (ep6_mI f i)
  | _, _, .apply o p d dOff s sOff cols => .apply (g o) (f p) d dOff s sOff cols
  | _, _, .rom p d i => .rom (f p) d i
  | _, _, .alloc p len b => .alloc (f p) len (ep6_map f g b)
  | _, _, .loop n b => .loop n (ep6_map f g b)
  | _, _, .whileFuel fu p c x y b => .whileFuel fu (f p) c x y (ep6_map f g b)
  | _, _, .ite p c x y t e => .ite (f p) c x y (ep6_map f g t) (ep6_map f g e)
  | _, _, .named n a b => .named n a (ep6_map f g b)
  | _, _, .kcall o p d i o' => .kcall (g o) (f p) d i o'
  | _, _, .bindIdx p x bd b => .bindIdx (f p) x bd (ep6_map f g b)

omit [DecidableEq P] in
set_option maxRecDepth 100000 in
/-- The registered tree is the tree at the tags `Unit` and oracle names `Bool`, renamed. -/
private theorem ep6_compiled_map (p : P) (mm qr : ι) : eighProg.compiled p mm qr =
    ep6_map (fun _ => p) (fun b => bif b then mm else qr) (eighProg.compiled () true false) := rfl

/-- A tree of kernel calls: the skeleton of a first-order tree that carries its kernel counts. -/
private inductive ep6_KT (P ι : Type) : ℕ → Type
  | skip {ni : ℕ} : ep6_KT P ι ni
  | seq {ni : ℕ} (a b : ep6_KT P ι ni) : ep6_KT P ι ni
  | loop {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι (ni + 1)) : ep6_KT P ι ni
  | rep {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι ni) : ep6_KT P ι ni
  | br {ni : ℕ} (a b : ep6_KT P ι ni) : ep6_KT P ι ni
  | bind {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι (ni + 1)) : ep6_KT P ι ni
  | call {ni : ℕ} (o : ι) (p : P) (d : List (IExp (Fin ni))) : ep6_KT P ι ni

private def ep6_sseq {P ι : Type} {ni : ℕ} : ep6_KT P ι ni → ep6_KT P ι ni → ep6_KT P ι ni
  | .skip, b => b
  | a, .skip => a
  | a, b => .seq a b

private def ep6_sloop {P ι : Type} {ni : ℕ} (n : IExp (Fin ni)) :
    ep6_KT P ι (ni + 1) → ep6_KT P ι ni
  | .skip => .skip
  | b => .loop n b

private def ep6_srep {P ι : Type} {ni : ℕ} (n : IExp (Fin ni)) : ep6_KT P ι ni → ep6_KT P ι ni
  | .skip => .skip
  | b => .rep n b

private def ep6_sbr {P ι : Type} {ni : ℕ} : ep6_KT P ι ni → ep6_KT P ι ni → ep6_KT P ι ni
  | .skip, b => b
  | a, .skip => a
  | a, b => .br a b

private def ep6_sbind {P ι : Type} {ni : ℕ} (n : IExp (Fin ni)) :
    ep6_KT P ι (ni + 1) → ep6_KT P ι ni
  | .skip => .skip
  | b => .bind n b

/-- The kernel calls of a tree. -/
private def ep6_prune {P ι : Type} : {nb ni : ℕ} → FStmt P ι nb ni → ep6_KT P ι ni
  | _, _, .seq s t => ep6_sseq (ep6_prune s) (ep6_prune t)
  | _, _, .alloc _ _ b => ep6_prune b
  | _, _, .loop n b => ep6_sloop n (ep6_prune b)
  | _, _, .whileFuel f _ _ _ _ b => ep6_srep f (ep6_prune b)
  | _, _, .ite _ _ _ _ t e => ep6_sbr (ep6_prune t) (ep6_prune e)
  | _, _, .named _ _ b => ep6_prune b
  | _, _, .kcall o p d _ _ => .call o p d
  | _, _, .bindIdx _ _ bd b => ep6_sbind bd (ep6_prune b)
  | _, _, _ => .skip

private def ep6_v {ni : ℕ} (i : ℕ) (h : i < ni := by decide) : IExp (Fin ni) := .var ⟨i, h⟩

/-- The split of a node (depth $10$ variables). -/
private def ep6_Dsplit {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 10 :=
  .seq (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5]) (.seq (.call qr p [ep6_v 5, ep6_v 5])
    (.seq (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5]) (.seq (.call qr p [ep6_v 5, ep6_v 5])
    (.seq (.call mm p [ep6_v 8, ep6_v 5, ep6_v 5]) (.seq (.call mm p [ep6_v 8, ep6_v 5, ep6_v 8])
    (.seq (.call mm p [.sub (ep6_v 5) (ep6_v 8), ep6_v 5, ep6_v 5])
      (.call mm p [.sub (ep6_v 5) (ep6_v 8), ep6_v 5, .sub (ep6_v 5) (ep6_v 8)])))))))

private def ep6_D9 {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 9 :=
  .loop (.sub (.const 1) (.sub (.const 1) (.mul (ep6_v 8) (.sub (ep6_v 5) (ep6_v 8)))))
    (ep6_Dsplit p mm qr)

private def ep6_D8 {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 8 :=
  .seq (.seq (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5])
      (.loop (ep6_v 2) (.seq (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5])
        (.call mm p [ep6_v 5, ep6_v 5, ep6_v 5]))))
    (.bind (ep6_v 5) (ep6_D9 p mm qr))

private def ep6_D6 {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 6 :=
  .loop (.sub (.const 1) (.sub (.const 1) (ep6_v 5)))
    (.loop (.sub (.const 1) (.sub (.const 1) (.sub (ep6_v 5) (.const 1)))) (ep6_D8 p mm qr))

private def ep6_U10 {P ι : Type} (p : P) (mm : ι) : ep6_KT P ι 10 :=
  .seq (.call mm p [ep6_v 5, ep6_v 9, ep6_v 9])
    (.call mm p [ep6_v 5, .sub (ep6_v 5) (ep6_v 9), .sub (ep6_v 5) (ep6_v 9)])

private def ep6_U9 {P ι : Type} (p : P) (mm : ι) : ep6_KT P ι 9 :=
  .bind (ep6_v 5) (ep6_U10 p mm)

private def ep6_U8 {P ι : Type} (p : P) (mm : ι) : ep6_KT P ι 8 :=
  .loop (.sub (.const 1) (.sub (.const 1)
    (.mul (.sub (.const 1) (.sub (ep6_v 7) (.const 4)))
      (.sub (.const 1) (.sub (.const 4) (ep6_v 7))))))
    (ep6_U9 p mm)

private def ep6_U6 {P ι : Type} (p : P) (mm : ι) : ep6_KT P ι 6 :=
  .loop (.sub (.const 1) (.sub (.const 1) (ep6_v 5))) (.bind (.const 4) (ep6_U8 p mm))

/-- The kernel calls of `NLAlib.eighProg.compiled`. -/
private def ep6_T {P ι : Type} (p : P) (mm qr : ι) : ep6_KT P ι 3 :=
  .seq (.loop (.add (ep6_v 1) (.const 1)) (.loop (ep6_v 0) (.bind (.sub (ep6_v 0) (ep6_v 4))
      (ep6_D6 p mm qr))))
    (.loop (.add (ep6_v 1) (.const 1)) (.loop (ep6_v 0) (.bind (.sub (ep6_v 0) (ep6_v 4))
      (ep6_U6 p mm))))

set_option maxRecDepth 100000 in
private theorem ep6_prune_compiled0 :
    ep6_prune (eighProg.compiled () true false) = ep6_T () true false := rfl

private theorem ep6_okC_compiled0 :
    ep6_okC (ep6_Cc (eighProg.compiled () true false) ep6_σ0) = true := by decide +kernel

private theorem ep6_okS_compiled0 : ∀ c ∈ [1, 2, 6, 7, 10, 11, 12, 13, 20, 23, 30, 32],
    ep6_okS (ep6_C c (eighProg.compiled () true false) ep6_σ0) = true := by decide +kernel

private theorem ep6_zero_compiled0 : ∀ c ∈ [3, 4, 5, 8, 14, 21, 31],
    ep6_C c (eighProg.compiled () true false) ep6_σ0 = [] := by decide +kernel

/-! #### Renaming -/

private theorem ep6_C_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') (c : ℕ) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (σ : Fin ni → ep6_Poly),
      ep6_C c (ep6_map f g s) σ = ep6_C c s σ := by
  intro nb ni s
  induction s with
  | instr i => intro σ; cases i <;> rfl
  | _ => intro σ; simp only [ep6_map, ep6_C, *]

private theorem ep6_Cc_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (σ : Fin ni → ep6_Poly),
      ep6_Cc (ep6_map f g s) σ = ep6_Cc s σ := by
  intro nb ni s
  induction s with
  | _ => intro σ; simp only [ep6_map, ep6_Cc, *]

private theorem ep6_tags_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni), ep6_tags (ep6_map f g s) = (ep6_tags s).map f := by
  intro nb ni s
  induction s with
  | instr i => cases i <;> rfl
  | _ => simp only [ep6_map, ep6_tags, List.map_append, List.map_cons, List.map_nil, *]

/-- Renaming a tree of kernel calls. -/
private def ep6_KTmap {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    {ni : ℕ} → ep6_KT P ι ni → ep6_KT P' ι' ni
  | _, .skip => .skip
  | _, .seq a b => .seq (ep6_KTmap f g a) (ep6_KTmap f g b)
  | _, .loop n b => .loop n (ep6_KTmap f g b)
  | _, .rep n b => .rep n (ep6_KTmap f g b)
  | _, .br a b => .br (ep6_KTmap f g a) (ep6_KTmap f g b)
  | _, .bind n b => .bind n (ep6_KTmap f g b)
  | _, .call o p d => .call (g o) (f p) d

private theorem ep6_prune_map {P P' ι ι' : Type} (f : P → P') (g : ι → ι') :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni),
      ep6_prune (ep6_map f g s) = ep6_KTmap f g (ep6_prune s) := by
  intro nb ni s
  induction s with
  | seq s t ihs iht =>
    simp only [ep6_map, ep6_prune, ihs, iht]
    cases ep6_prune s <;> cases ep6_prune t <;> rfl
  | loop n b ih =>
    simp only [ep6_map, ep6_prune, ih]
    cases ep6_prune b <;> rfl
  | whileFuel fu p c x y b ih =>
    simp only [ep6_map, ep6_prune, ih]
    cases ep6_prune b <;> rfl
  | ite p c x y t e iht ihe =>
    simp only [ep6_map, ep6_prune, iht, ihe]
    cases ep6_prune t <;> cases ep6_prune e <;> rfl
  | bindIdx p x bd b ih =>
    simp only [ep6_map, ep6_prune, ih]
    cases ep6_prune b <;> rfl
  | alloc p len b ih => simp only [ep6_map, ep6_prune, ih]
  | named n a b ih => simp only [ep6_map, ep6_prune, ih]
  | _ => rfl

omit [DecidableEq P] in
private theorem ep6_prune_compiled (p : P) (mm qr : ι) :
    ep6_prune (eighProg.compiled p mm qr) = ep6_T p mm qr := by
  rw [ep6_compiled_map, ep6_prune_map, ep6_prune_compiled0]
  rfl


/-! #### The kernel counts of a tree of kernel calls -/

/-- The static kernel count of a tree of kernel calls, as `NLAlib.Computation.FStmt.staticCost`
counts it. -/
private noncomputable def ep6_kc {P ι : Type} : {ni : ℕ} → ep6_KT P ι ni → (Fin ni → ℕ) →
    OpCount P ι
  | _, .skip, _ => 0
  | _, .seq a b, ρ => ep6_kc a ρ + ep6_kc b ρ
  | _, .loop n b, ρ =>
      ((List.range (n.evalIn ρ)).map fun i => ep6_kc b (Fin.snoc (α := fun _ => ℕ) ρ i)).sum
  | _, .rep n b, ρ => n.evalIn ρ • ep6_kc b ρ
  | _, .br a b, ρ => ep6_kc a ρ ⊔ ep6_kc b ρ
  | _, .bind n b, ρ => (List.range (n.evalIn ρ + 1)).foldr
      (fun k c => ep6_kc b (Fin.snoc (α := fun _ => ℕ) ρ k) ⊔ c) 0
  | _, .call o p d, ρ => Finsupp.single (.kcall p o (d.map (·.evalIn ρ))) 1

omit [DecidableEq P] in
private theorem ep6_foldr_zero (l : List ℕ) :
    l.foldr (fun _ c => (0 : OpCount P ι) ⊔ c) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

omit [DecidableEq P] in
private theorem ep6_kc_sseq {ni : ℕ} (a b : ep6_KT P ι ni) (ρ : Fin ni → ℕ) :
    ep6_kc (ep6_sseq a b) ρ = ep6_kc a ρ + ep6_kc b ρ := by
  unfold ep6_sseq
  split <;> simp [ep6_kc]

omit [DecidableEq P] in
private theorem ep6_kc_sbr {ni : ℕ} (a b : ep6_KT P ι ni) (ρ : Fin ni → ℕ) :
    ep6_kc (ep6_sbr a b) ρ = ep6_kc a ρ ⊔ ep6_kc b ρ := by
  unfold ep6_sbr
  split <;> simp [ep6_kc]

omit [DecidableEq P] in
private theorem ep6_kc_sloop {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι (ni + 1))
    (ρ : Fin ni → ℕ) : ep6_kc (ep6_sloop n b) ρ = ep6_kc (.loop n b) ρ := by
  unfold ep6_sloop
  split <;> simp [ep6_kc]

omit [DecidableEq P] in
private theorem ep6_kc_srep {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι ni)
    (ρ : Fin ni → ℕ) : ep6_kc (ep6_srep n b) ρ = ep6_kc (.rep n b) ρ := by
  unfold ep6_srep
  split <;> simp [ep6_kc]

omit [DecidableEq P] in
private theorem ep6_kc_sbind {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι (ni + 1))
    (ρ : Fin ni → ℕ) : ep6_kc (ep6_sbind n b) ρ = ep6_kc (.bind n b) ρ := by
  unfold ep6_sbind
  split
  · simp only [ep6_kc]; exact (ep6_foldr_zero _).symm
  · rfl

omit [DecidableEq P] in
private theorem ep6_lsum_apply (l : List ℕ) (f : ℕ → OpCount P ι) (κ : OpKind P ι) :
    (l.map f).sum κ = (l.map fun i => f i κ).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

omit [DecidableEq P] in
private theorem ep6_supRange_count_eq {f : ℕ → StaticCost P ι} {g : ℕ → OpCount P ι} {m : ℕ}
    {κ : OpKind P ι} (h : ∀ k, (f k).count κ = g k κ) :
    (StaticCost.supRange m f).count κ = (List.range m).foldr (fun k c => g k ⊔ c) 0 κ := by
  unfold StaticCost.supRange
  induction List.range m with
  | nil => rfl
  | cons a l ih =>
    change ((f a).count ⊔ (l.foldr (fun k c => (f k).branch c) StaticCost.zero).count) κ =
      (g a ⊔ l.foldr (fun k c => g k ⊔ c) 0) κ
    rw [Finsupp.sup_apply, Finsupp.sup_apply, h, ih]

omit [DecidableEq P] in
private theorem ep6_single_zero {k κ : OpKind P ι} (h : ep6_cls k ≠ ep6_cls κ) :
    (Finsupp.single k 1 : OpCount P ι) κ = 0 := by
  classical
  rw [Finsupp.single_apply, if_neg]
  rintro rfl
  exact h rfl

omit [DecidableEq P] in
private theorem ep6_cls_instr (i : Instr P ℕ ℕ) : ep6_cls (i.kind (ι := ι)) ≠ 9 := by
  cases i <;> simp only [Instr.kind, ep6_cls] <;> first | decide | (split <;> decide)

/-- **The kernel counts are those of the tree of kernel calls.** -/
private theorem ep6_count_prune (w : P → ℕ) (κ : OpKind P ι) (h9 : ep6_cls κ = 9) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ),
      (s.staticCost (fun k => Finsupp.single k 1) w ρ).count κ = ep6_kc (ep6_prune s) ρ κ := by
  have hz : ∀ k : OpKind P ι, ep6_cls k ≠ 9 → (Finsupp.single k 1 : OpCount P ι) κ = 0 :=
    fun k hk => ep6_single_zero (h9 ▸ hk)
  intro nb ni s
  induction s with
  | skip => intro ρ; rfl
  | seq s t ihs iht =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.seq, Finsupp.add_apply, ep6_prune, ep6_kc_sseq, ihs,
      iht]
  | instr i =>
    intro ρ
    exact hz _ (ep6_cls_instr _)
  | apply o p d dOff s sOff cols =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.step, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul, ep6_prune, ep6_kc, Finsupp.zero_apply]
    rw [hz _ (by simp [ep6_cls]), hz _ (by simp [ep6_cls])]
    simp
  | rom p d i =>
    intro ρ
    exact hz _ (by simp [ep6_cls])
  | alloc p len body ih =>
    intro ρ
    exact ih ρ
  | loop n body ih =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.sequence_count_apply, ep6_prune, ep6_kc_sloop,
      ep6_kc, ep6_lsum_apply, ih]
  | whileFuel fuel p c x y body ih =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, ep6_prune, ep6_kc_srep, ep6_kc, ih,
      hz (.cmp p) (by simp [ep6_cls]), zero_add]
  | ite p c x y t e iht ihe =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.branch, StaticCost.seq, StaticCost.step,
      Finsupp.add_apply, Finsupp.sup_apply, ep6_prune, ep6_kc_sbr, iht, ihe,
      hz (.cmp p) (by simp [ep6_cls]), zero_add]
  | named name args body ih =>
    intro ρ
    exact ih ρ
  | kcall o p dims ins outs =>
    intro ρ
    rfl
  | bindIdx p x bound body ih =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, Finsupp.add_apply,
      hz (.toNat p) (by simp [ep6_cls]), zero_add, ep6_prune, ep6_kc_sbind, ep6_kc]
    exact ep6_supRange_count_eq fun k => ih _

/-! #### The polynomial checks -/

private theorem ep6_ev_le_mul (N L F M : ℕ) (p : ep6_Poly)
    (h : ∀ e ∈ p, N ^ e.2.1 * L ^ e.2.2.1 * F ^ e.2.2.2 ≤ M) :
    ep6_ev N L F p ≤ (p.map (·.1)).sum * M := by
  induction p with
  | nil => simp [ep6_ev]
  | cons a p ih =>
    have ih' := ih fun e he => h e (List.mem_cons_of_mem a he)
    simp only [ep6_ev, List.map_cons, List.sum_cons, add_mul] at ih' ⊢
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (h a List.mem_cons_self)) ih'

private theorem ep6_pow_le_succ (L b : ℕ) (hb : b ≤ 1) : L ^ b ≤ L + 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp

private theorem ep6_okS_le (N L F : ℕ) (p : ep6_Poly) (h : ep6_okS p = true) :
    ep6_ev N L F p ≤ 1024 * (F + 2) * (L + 2) * (N + 1) ^ 3 := by
  simp only [ep6_okS, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hall, hsum⟩ := h
  refine (ep6_ev_le_mul N L F ((N + 1) ^ 3 * (L + 1) * (F + 1)) p fun e he => ?_).trans ?_
  · obtain ⟨⟨ha, hb⟩, hc⟩ := hall e he
    refine Nat.mul_le_mul (Nat.mul_le_mul ?_ (ep6_pow_le_succ L _ hb)) (ep6_pow_le_succ F _ hc)
    exact (Nat.pow_le_pow_left (Nat.le_succ N) _).trans (Nat.pow_le_pow_right (by omega) ha)
  · calc (p.map (·.1)).sum * ((N + 1) ^ 3 * (L + 1) * (F + 1))
        ≤ 1024 * ((N + 1) ^ 3 * (L + 1) * (F + 1)) := Nat.mul_le_mul_right _ hsum
      _ ≤ 1024 * (F + 2) * (L + 2) * (N + 1) ^ 3 := by
        have h1 : (L + 1) * (F + 1) ≤ (L + 2) * (F + 2) := Nat.mul_le_mul (by omega) (by omega)
        have h2 := Nat.mul_le_mul_left (1024 * (N + 1) ^ 3) h1
        calc 1024 * ((N + 1) ^ 3 * (L + 1) * (F + 1))
            = 1024 * (N + 1) ^ 3 * ((L + 1) * (F + 1)) := by ring
          _ ≤ 1024 * (N + 1) ^ 3 * ((L + 2) * (F + 2)) := h2
          _ = 1024 * (F + 2) * (L + 2) * (N + 1) ^ 3 := by ring

private theorem ep6_okC_le (N L F : ℕ) (p : ep6_Poly) (h : ep6_okC p = true) :
    ep6_ev N L F p ≤ 64 * (N + 1) ^ 2 * (L + 3) := by
  simp only [ep6_okC, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hall, h0⟩, h1⟩ := h
  have key : ep6_ev N L F p ≤ (N + 1) ^ 2 * ((p.map fun e => if e.2.2.1 = 0 then e.1 else 0).sum +
      (p.map fun e => if e.2.2.1 = 0 then 0 else e.1).sum * L) := by
    clear h0 h1
    induction p with
    | nil => simp [ep6_ev]
    | cons a p ih =>
      have ih' := ih fun e he => hall e (List.mem_cons_of_mem a he)
      obtain ⟨⟨ha, hb⟩, hc⟩ := hall a List.mem_cons_self
      simp only [ep6_ev, List.map_cons, List.sum_cons] at ih' ⊢
      have hN : N ^ a.2.1 ≤ (N + 1) ^ 2 :=
        (Nat.pow_le_pow_left (Nat.le_succ N) _).trans (Nat.pow_le_pow_right (by omega) ha)
      have hterm : a.1 * (N ^ a.2.1 * L ^ a.2.2.1 * F ^ a.2.2.2) ≤
          (N + 1) ^ 2 * ((if a.2.2.1 = 0 then a.1 else 0) +
            (if a.2.2.1 = 0 then 0 else a.1) * L) := by
        rw [hc, pow_zero, mul_one]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb0 | hb1
        · simp only [hb0, pow_zero, mul_one, if_true, zero_mul, add_zero]
          calc a.1 * N ^ a.2.1 ≤ a.1 * (N + 1) ^ 2 := Nat.mul_le_mul_left _ hN
            _ = (N + 1) ^ 2 * a.1 := Nat.mul_comm _ _
        · simp only [hb1, pow_one, one_ne_zero, if_false, zero_add]
          calc a.1 * (N ^ a.2.1 * L) ≤ a.1 * ((N + 1) ^ 2 * L) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hN)
            _ = (N + 1) ^ 2 * (a.1 * L) := by ring
      calc a.1 * (N ^ a.2.1 * L ^ a.2.2.1 * F ^ a.2.2.2) + ep6_ev N L F p
          ≤ _ + _ := Nat.add_le_add hterm ih'
        _ = _ := by ring
  refine key.trans ?_
  calc (N + 1) ^ 2 * (_ + _ * L) ≤ (N + 1) ^ 2 * (192 + 64 * L) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add h0 (Nat.mul_le_mul_right _ h1))
    _ = 64 * (N + 1) ^ 2 * (L + 3) := by ring

/-! #### The kernel bound -/

/-- The kernel calls charged by `NLAlib.eighCount` for a node of size $k$ split at $k_+$. -/
private noncomputable def ep6_G (p : P) (mm qr : ι) (F k kp : ℕ) : OpCount P ι :=
  (2 * F + 8) • Finsupp.single (.kcall p mm [k, k, k]) 1 +
    Finsupp.single (.kcall p qr [k, k]) 2 +
    Finsupp.single (.kcall p mm [kp, k, k]) 1 + Finsupp.single (.kcall p mm [kp, k, kp]) 1 +
    Finsupp.single (.kcall p mm [k - kp, k, k]) 1 +
    Finsupp.single (.kcall p mm [k - kp, k, k - kp]) 1 +
    Finsupp.single (.kcall p mm [k, kp, kp]) 1 +
    Finsupp.single (.kcall p mm [k, k - kp, k - kp]) 1

/-- The kernel calls charged for a node of size $k$, every split. -/
private noncomputable def ep6_Gk (p : P) (mm qr : ι) (F k : ℕ) : OpCount P ι :=
  ∑ kp ∈ Finset.range (k + 1), ep6_G p mm qr F k kp

omit [DecidableEq P] in
private theorem ep6_eighCount_eq (p : P) (mm qr : ι) (n L F : ℕ) :
    eighCount p mm qr n L F = ((eighScalarKinds (ι := ι) p).map fun κ =>
      Finsupp.single κ (1024 * (F + 2) * (L + 2) * (n + 1) ^ 3)).sum +
      (2 * (L + 1) * n) • ∑ k ∈ Finset.range (n + 1), ep6_Gk p mm qr F k := rfl

omit [DecidableEq P] in
private theorem ep6_lsum_le (m : ℕ) (f : ℕ → OpCount P ι) (B : OpCount P ι)
    (h : ∀ i < m, f i ≤ B) : ((List.range m).map f).sum ≤ m • B := by
  simpa using ep6_sum_le (List.range m) f B fun i hi => h i (List.mem_range.mp hi)

omit [DecidableEq P] in
private theorem ep6_trip_le {m : ℕ} (hm : m ≤ 1) (f : ℕ → OpCount P ι) :
    ((List.range m).map f).sum ≤ f 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp

omit [DecidableEq P] in
private theorem ep6_fsup_le (l : List ℕ) (f : ℕ → OpCount P ι) (B : OpCount P ι)
    (h : ∀ k ∈ l, f k ≤ B) : l.foldr (fun k c => f k ⊔ c) 0 ≤ B := by
  induction l with
  | nil => exact zero_le
  | cons a l ih =>
    exact sup_le (h a List.mem_cons_self) (ih fun k hk => h k (List.mem_cons_of_mem a hk))

omit [DecidableEq P] in
private theorem ep6_fsup_le_sum (m : ℕ) (f : ℕ → OpCount P ι) :
    (List.range m).foldr (fun k c => f k ⊔ c) 0 ≤ ∑ k ∈ Finset.range m, f k :=
  ep6_fsup_le _ _ _ fun _ hk => Finset.single_le_sum (fun _ _ => zero_le)
    (Finset.mem_range.mpr (List.mem_range.mp hk))

omit [DecidableEq P] in
private theorem ep6_Dsplit_le (p : P) (mm qr : ι) (ρ : Fin 10 → ℕ) :
    (2 * ρ ⟨2, by decide⟩ + 6) • Finsupp.single (OpKind.kcall p mm
      [ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩]) 1 +
      ep6_kc (ep6_Dsplit p mm qr) ρ ≤
      ep6_G p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) (ρ ⟨8, by decide⟩) := by
  simp only [ep6_Dsplit, ep6_kc, ep6_v, IExp.evalIn, List.map_cons, List.map_nil, ep6_G]
  generalize ρ ⟨2, by decide⟩ = F
  generalize ρ ⟨5, by decide⟩ = k
  generalize ρ ⟨8, by decide⟩ = kp
  have e2 : Finsupp.single (OpKind.kcall p qr [k, k]) 2 =
      Finsupp.single (OpKind.kcall p qr [k, k]) 1 +
        Finsupp.single (OpKind.kcall p qr [k, k]) 1 := by
    rw [← Finsupp.single_add]
  rw [e2]
  refine (le_self_add (b := Finsupp.single (OpKind.kcall p mm [k, kp, kp]) 1 +
    Finsupp.single (OpKind.kcall p mm [k, k - kp, k - kp]) 1)).trans_eq ?_
  ext κ
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq P] in
private theorem ep6_D9_le (p : P) (mm qr : ι) (ρ : Fin 9 → ℕ) :
    (2 * ρ ⟨2, by decide⟩ + 6) • Finsupp.single (OpKind.kcall p mm
      [ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩]) 1 +
      ep6_kc (ep6_D9 p mm qr) ρ ≤
      ep6_G p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) (ρ ⟨8, by decide⟩) := by
  simp only [ep6_D9, ep6_kc]
  refine (add_le_add le_rfl (ep6_trip_le (Nat.sub_le _ _) _)).trans ?_
  exact ep6_Dsplit_le p mm qr (Fin.snoc ρ 0)

omit [DecidableEq P] in
private theorem ep6_D8_le (p : P) (mm qr : ι) (ρ : Fin 8 → ℕ) :
    ep6_kc (ep6_D8 p mm qr) ρ ≤ ep6_Gk p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) := by
  simp only [ep6_D8, ep6_kc, ep6_v, IExp.evalIn, List.map_cons, List.map_nil]
  set F := ρ ⟨2, by decide⟩
  set k := ρ ⟨5, by decide⟩
  set s := Finsupp.single (OpKind.kcall p mm [k, k, k]) (1 : ℕ)
  have h1 : s + ((List.range F).map fun _ => s + s).sum ≤ (2 * F + 6) • s := by
    rw [List.map_const', List.sum_replicate, List.length_range]
    have : s + F • (s + s) = (2 * F + 1) • s := by
      ext κ; simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact nsmul_le_nsmul_left zero_le (by omega)
  refine (add_le_add h1 le_rfl).trans ?_
  have hX : ∀ kp, (2 * F + 6) • s + ep6_kc (ep6_D9 p mm qr) (Fin.snoc (α := fun _ => ℕ) ρ kp) ≤
      ep6_G p mm qr F k kp := fun kp => ep6_D9_le p mm qr (Fin.snoc ρ kp)
  refine (add_le_add le_rfl (ep6_fsup_le_sum _ _)).trans ?_
  unfold ep6_Gk
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  calc (2 * F + 6) • s + (∑ i ∈ Finset.range k, ep6_kc (ep6_D9 p mm qr)
        (Fin.snoc (α := fun _ => ℕ) ρ (i + 1)) +
        ep6_kc (ep6_D9 p mm qr) (Fin.snoc (α := fun _ => ℕ) ρ 0))
      = (∑ i ∈ Finset.range k, ep6_kc (ep6_D9 p mm qr) (Fin.snoc (α := fun _ => ℕ) ρ (i + 1))) +
        ((2 * F + 6) • s + ep6_kc (ep6_D9 p mm qr) (Fin.snoc (α := fun _ => ℕ) ρ 0)) := by abel
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun i _ => le_add_self.trans (hX (i + 1))) (hX 0)

omit [DecidableEq P] in
private theorem ep6_D6_le (p : P) (mm qr : ι) (ρ : Fin 6 → ℕ) :
    ep6_kc (ep6_D6 p mm qr) ρ ≤ ep6_Gk p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) := by
  simp only [ep6_D6, ep6_kc]
  refine (ep6_trip_le (Nat.sub_le _ _) _).trans ?_
  refine (ep6_trip_le (Nat.sub_le _ _) _).trans ?_
  exact ep6_D8_le p mm qr _

omit [DecidableEq P] in
private theorem ep6_U10_le (p : P) (mm qr : ι) (ρ : Fin 10 → ℕ) :
    ep6_kc (ep6_U10 p mm) ρ ≤
      ep6_G p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) (ρ ⟨9, by decide⟩) := by
  simp only [ep6_U10, ep6_kc, ep6_v, IExp.evalIn, List.map_cons, List.map_nil, ep6_G]
  rw [add_assoc _ (Finsupp.single _ 1) (Finsupp.single _ 1)]
  exact le_add_self

omit [DecidableEq P] in
private theorem ep6_U6_le (p : P) (mm qr : ι) (ρ : Fin 6 → ℕ) :
    ep6_kc (ep6_U6 p mm) ρ ≤ ep6_Gk p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) := by
  simp only [ep6_U6, ep6_kc]
  refine (ep6_trip_le (Nat.sub_le _ _) _).trans ?_
  refine ep6_fsup_le _ _ _ fun c _ => ?_
  simp only [ep6_U8, ep6_kc]
  refine (ep6_trip_le (Nat.sub_le _ _) _).trans ?_
  simp only [ep6_U9, ep6_kc]
  refine ep6_fsup_le _ _ _ fun kp hkp => ?_
  refine (ep6_U10_le p mm qr _).trans ?_
  exact Finset.single_le_sum (f := fun kp => ep6_G p mm qr _ _ kp) (fun _ _ => zero_le)
    (Finset.mem_range.mpr (List.mem_range.mp hkp))

omit [DecidableEq P] in
/-- **The kernel calls of the registered tree** are at most those of `NLAlib.eighCount`. -/
private theorem ep6_T_le (p : P) (mm qr : ι) (N L F : ℕ) :
    ep6_kc (ep6_T p mm qr) (Fin.cons N ![L, F]) ≤
      (2 * (L + 1) * N) • ∑ k ∈ Finset.range (N + 1), ep6_Gk p mm qr F k := by
  set Gs := ∑ k ∈ Finset.range (N + 1), ep6_Gk p mm qr F k
  have hG : ∀ k ≤ N, ep6_Gk p mm qr F k ≤ Gs := fun k hk =>
    Finset.single_le_sum (f := fun k => ep6_Gk p mm qr F k) (fun _ _ => zero_le)
      (Finset.mem_range.mpr (by omega))
  have hlev : ∀ (X : ep6_KT P ι 6), (∀ ρ : Fin 6 → ℕ, ρ ⟨2, by decide⟩ = F → ρ ⟨5, by decide⟩ ≤ N →
      ep6_kc X ρ ≤ Gs) →
      ep6_kc (ep6_KT.loop (.add (ep6_v 1) (.const 1)) (.loop (ep6_v 0)
        (.bind (.sub (ep6_v 0) (ep6_v 4)) X))) (Fin.cons N ![L, F]) ≤ (L + 1) • N • Gs := by
    intro X hX
    simp only [ep6_kc]
    refine ep6_lsum_le _ _ _ fun d _ => ?_
    refine ep6_lsum_le _ _ _ fun lo _ => ?_
    refine ep6_fsup_le _ _ _ fun k hk => hX _ rfl ?_
    have := List.mem_range.mp hk
    simp only [IExp.evalIn, ep6_v] at this
    change k ≤ N
    have h0 : (Fin.snoc (α := fun _ => ℕ) (Fin.snoc (α := fun _ => ℕ)
        (Fin.cons N ![L, F] : Fin 3 → ℕ) d) lo) ⟨0, by decide⟩ = N := rfl
    rw [h0] at this
    omega
  simp only [ep6_T, ep6_kc]
  refine (add_le_add (hlev _ fun ρ hF hk => (ep6_D6_le p mm qr ρ).trans (hF ▸ hG _ hk))
    (hlev _ fun ρ hF hk => (ep6_U6_le p mm qr ρ).trans (hF ▸ hG _ hk))).trans_eq ?_
  rw [smul_smul, ← add_nsmul]
  congr 1
  ring

/-! #### Assembly -/

private theorem ep6_ρ0 (N L F : ℕ) :
    ∀ v, (Fin.cons N ![L, F] : Fin 3 → ℕ) v ≤ ep6_ev N L F (ep6_σ0 v) := by
  intro v
  fin_cases v <;> simp [ep6_σ0, ep6_ev]

omit [DecidableEq P] in
private theorem ep6_scalar_ge (p : P) (mm qr : ι) (n L F : ℕ) {κ : OpKind P ι}
    (hκ : κ ∈ eighScalarKinds (ι := ι) p) :
    1024 * (F + 2) * (L + 2) * (n + 1) ^ 3 ≤ eighCount p mm qr n L F κ := by
  rw [ep6_eighCount_eq, Finsupp.add_apply]
  refine le_trans ?_ (Nat.le_add_right _ _)
  have h := List.single_le_sum (fun _ _ => zero_le) _
    (List.mem_map_of_mem (f := fun κ : OpKind P ι =>
      Finsupp.single κ (1024 * (F + 2) * (L + 2) * (n + 1) ^ 3)) hκ)
  simpa using h κ

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
omit [DecidableEq P] in
private theorem ep6_scalar_bound (p : P) (mm qr : ι) (N L F : ℕ) (κ : OpKind P ι)
    (h9 : ep6_cls κ ≠ 9) (ht : ep6_ktag κ = p) :
    ep6_ev N L F (ep6_C (ep6_cls κ) (eighProg.compiled () true false) ep6_σ0) ≤
      eighCount p mm qr N L F κ := by
  have hz : ∀ c ∈ [3, 4, 5, 8, 14, 21, 31], c = ep6_cls κ →
      ep6_ev N L F (ep6_C (ep6_cls κ) (eighProg.compiled () true false) ep6_σ0) ≤
        eighCount p mm qr N L F κ := by
    intro c hc he
    rw [← he, ep6_zero_compiled0 c hc]
    simp [ep6_ev]
  have hs : ∀ c ∈ [1, 2, 6, 7, 10, 11, 12, 13, 20, 23, 30, 32], c = ep6_cls κ →
      κ ∈ eighScalarKinds (ι := ι) p →
      ep6_ev N L F (ep6_C (ep6_cls κ) (eighProg.compiled () true false) ep6_σ0) ≤
        eighCount p mm qr N L F κ := by
    intro c hc he hk
    rw [← he]
    exact (ep6_okS_le N L F _ (ep6_okS_compiled0 c hc)).trans (ep6_scalar_ge p mm qr N L F hk)
  cases κ with
  | bin q b =>
    simp only [ep6_ktag] at ht; subst ht
    cases b <;> first
      | exact hz 3 (by simp) rfl
      | exact hz 4 (by simp) rfl
      | exact hz 5 (by simp) rfl
      | exact hz 8 (by simp) rfl
      | exact hz 14 (by simp) rfl
      | exact hz 21 (by simp) rfl
      | exact hz 31 (by simp) rfl
      | exact hs 1 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 2 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 6 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 7 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 10 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 11 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 12 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 13 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 20 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 23 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 30 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 32 (by simp) rfl (by simp [eighScalarKinds])
  | un q u =>
    simp only [ep6_ktag] at ht; subst ht
    cases u <;> first
      | exact hz 3 (by simp) rfl
      | exact hz 4 (by simp) rfl
      | exact hz 5 (by simp) rfl
      | exact hz 8 (by simp) rfl
      | exact hz 14 (by simp) rfl
      | exact hz 21 (by simp) rfl
      | exact hz 31 (by simp) rfl
      | exact hs 1 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 2 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 6 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 7 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 10 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 11 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 12 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 13 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 20 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 23 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 30 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 32 (by simp) rfl (by simp [eighScalarKinds])
  | draw q d =>
    simp only [ep6_ktag] at ht; subst ht
    cases d <;> first
      | exact hz 3 (by simp) rfl
      | exact hz 4 (by simp) rfl
      | exact hz 5 (by simp) rfl
      | exact hz 8 (by simp) rfl
      | exact hz 14 (by simp) rfl
      | exact hz 21 (by simp) rfl
      | exact hz 31 (by simp) rfl
      | exact hs 1 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 2 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 6 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 7 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 10 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 11 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 12 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 13 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 20 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 23 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 30 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 32 (by simp) rfl (by simp [eighScalarKinds])
  | kcall q o d => exact absurd rfl h9
  | _ =>
    simp only [ep6_ktag] at ht; subst ht
    first
      | exact hz 3 (by simp) rfl
      | exact hz 4 (by simp) rfl
      | exact hz 5 (by simp) rfl
      | exact hz 8 (by simp) rfl
      | exact hz 14 (by simp) rfl
      | exact hz 21 (by simp) rfl
      | exact hz 31 (by simp) rfl
      | exact hs 1 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 2 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 6 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 7 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 10 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 11 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 12 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 13 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 20 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 23 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 30 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 32 (by simp) rfl (by simp [eighScalarKinds])

omit [DecidableEq P] in
set_option maxRecDepth 100000 in
private theorem ep6_tags_compiled (p : P) (mm qr : ι) :
    ∀ q ∈ ep6_tags (eighProg.compiled p mm qr), q = p := by
  rw [ep6_compiled_map, ep6_tags_map]
  intro q hq
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
  rfl

omit [DecidableEq P] in
set_option maxRecDepth 100000 in
private theorem ep6_C_compiled (p : P) (mm qr : ι) (c : ℕ) :
    ep6_C c (eighProg.compiled p mm qr) ep6_σ0 =
      ep6_C c (eighProg.compiled () true false) ep6_σ0 := by
  rw [ep6_compiled_map, ep6_C_map]

omit [DecidableEq P] in
set_option maxRecDepth 100000 in
private theorem ep6_Cc_compiled (p : P) (mm qr : ι) :
    ep6_Cc (eighProg.compiled p mm qr) ep6_σ0 =
      ep6_Cc (eighProg.compiled () true false) ep6_σ0 := by
  rw [ep6_compiled_map, ep6_Cc_map]

private theorem ep6_count_bound (w : P → ℕ) (p : P) (mm qr : ι) (N L F : ℕ)
    (T : FStmt P ι 4 3) (hpr : ep6_prune T = ep6_T p mm qr)
    (hC : ∀ c, ep6_C c T ep6_σ0 = ep6_C c (eighProg.compiled () true false) ep6_σ0)
    (htag : ∀ q ∈ ep6_tags T, q = p) (κ : OpKind P ι) :
    (FStmt.staticCost (fun k => Finsupp.single k 1) w T (Fin.cons N ![L, F])).count κ ≤
      eighCount p mm qr N L F κ := by
  by_cases h9 : ep6_cls κ = 9
  · rw [ep6_count_prune w κ h9, hpr, ep6_eighCount_eq, Finsupp.add_apply]
    exact (ep6_T_le p mm qr N L F κ).trans (Nat.le_add_left _ _)
  · by_cases ht : ep6_ktag κ = p
    · refine (ep6_count_le w κ N L F T _ ep6_σ0 (ep6_ρ0 N L F)).trans ?_
      rw [hC]
      exact ep6_scalar_bound p mm qr N L F κ h9 ht
    · have := ep6_count_tag w κ T (Fin.cons N ![L, F]) fun hm => ht (htag _ hm)
      omega

private theorem ep6_cells_bound (charge : OpKind P ι → OpCount P ι) (w : P → ℕ) (p : P)
    (N L F : ℕ) (T : FStmt P ι 4 3)
    (hC : ep6_Cc T ep6_σ0 = ep6_Cc (eighProg.compiled () true false) ep6_σ0)
    (htag : ∀ q ∈ ep6_tags T, q = p) (q : P) :
    (FStmt.staticCost charge w T (Fin.cons N ![L, F])).cells q ≤
      if q = p then 64 * (N + 1) ^ 2 * (L + 3) else 0 := by
  split_ifs with hq
  · refine (ep6_cells_le charge w q N L F T _ ep6_σ0 (ep6_ρ0 N L F)).trans ?_
    rw [hC]
    exact ep6_okC_le N L F _ ep6_okC_compiled0
  · exact ep6_cells_tag charge w q _ _ fun hm => hq (htag _ hm)

/-- **The counts and the memory of the registered tree**: under the standard charge (one per
operation), every successful run of `NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$
adds at most `NLAlib.eighCount p mm qr N ℓ₀ F` to the counts and raises the peak memory at tag `p`
by at most $64(N + 1)^2(\ell_0 + 3)$ cells above the current memory (by nothing at any other tag):
the arenas of $D + 1 = \ell_0 + 2$ levels and the scratch of one node, $O(N^2 \ell_0)$. No printed
source.
Proof: `NLAlib.Computation.Prog.bounds_staticCost_of_exec_eq_some`; the static cost of the tree is
computed by `NLAlib.Computation.FStmt.staticCost` (`simp` with
`NLAlib.Computation.StaticCost.seq`, `NLAlib.Computation.StaticCost.sequence`,
`NLAlib.Computation.StaticCost.branch`, `NLAlib.Computation.StaticCost.supRange`,
`NLAlib.Computation.StaticCost.alloc`): each slot visit is bounded by the supremum over the node
sizes $k \le N$ and splits $k_+ \le k$, which is at most their sum (`Finset.sum_le_sum`,
`le_sup_iff`-style bounds of `NLAlib.Computation.StaticCost.supRange` by a sum of nonnegative
terms); the scalar kinds are at most $1024(F + 2)(\ell_0 + 2)(N + 1)^3$ each; compare kind by kind
(`Finsupp.le_def`). M, about 120 lines. -/
theorem eighProg.cnt_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (N ℓ₀ F : ℕ)
    {st st' : St P K (OpCount P ι)}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F] st = some st') :
    st'.cnt ≤ st.cnt + eighCount p mm qr N ℓ₀ F ∧
      ∀ q, st'.peak q ≤ max (st.peak q)
        (st.cur q + if q = p then 64 * (N + 1) ^ 2 * (ℓ₀ + 3) else 0) := by
  have hb := (eighProg.compiled p mm qr).bounds_staticCost_of_exec_eq_some I N ![ℓ₀, F] h
  have hpr := ep6_prune_compiled p mm qr
  have hC := ep6_C_compiled p mm qr
  have hCc := ep6_Cc_compiled p mm qr
  have htag := ep6_tags_compiled p mm qr
  generalize eighProg.compiled p mm qr = T at hb hpr hC hCc htag
  have hcharge : I.charge = fun k => Finsupp.single k 1 := funext hc
  have hcount := ep6_count_bound I.width p mm qr N ℓ₀ F T hpr hC htag
  rw [← hcharge] at hcount
  exact ⟨hb.count.trans (add_le_add le_rfl fun κ => hcount κ), fun q => (hb.peak q).trans
    (max_le_max le_rfl
      (add_le_add le_rfl (ep6_cells_bound I.charge I.width p N ℓ₀ F T hCc htag q)))⟩

/-! ### EP7 helpers

The weighted kernel count of a run, by an invariant of the run: `ep7_HT` is a Hoare triple
for the cost and for the cells of one tracked buffer (the size arena `Sz`); `ep7_BW` is the
same for a builder that keeps the tracked buffer, through any continuation. -/

section EP7

omit [AddMonoid C] [Inhabited K]

/-- The weight of an operation kind: `T` of the largest dimension of a kernel call. -/
private def ep7_wt (T : ℕ → ℕ) : OpKind P ι → ℕ
  | .kcall _ _ ds => T (ds.foldr max 0)
  | _ => 0

/-- The cells of buffer `b` at tag `p`. -/
private def ep7_V (s : Store P K) (p : P) (b : ℕ) : ℕ → Option K := fun i => s.read p b i

/-- Every successful run of `s` from a state whose buffer `b` reads `V₀` adds at most `c T(m)` to
the weighted count and ends with buffer `b` satisfying `Q`. -/
private def ep7_HT (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (p : P) (b m : ℕ)
    (V₀ : ℕ → Option K) (s : Stmt P ι ℕ ℕ) (c : ℕ) (Q : (ℕ → Option K) → Prop) : Prop :=
  Monotone T → (∀ κ, I.charge κ = Finsupp.single κ 1) → ∀ st st' : St P K (OpCount P ι),
    b < st.store.size → ep7_V st.store p b = V₀ → exec I s st = some st' →
    Finsupp.weight (ep7_wt T) st'.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt + c * T m ∧
      Q (ep7_V st'.store p b)

/-- A statement that keeps buffer `b` and costs at most `c T(m)`. -/
private def ep7_SF (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (p : P) (b m : ℕ)
    (s : Stmt P ι ℕ ℕ) (c : ℕ) : Prop :=
  ∀ V₀, ep7_HT I T p b m V₀ s c (· = V₀)

/-- The run of a builder with a continuation. -/
private def ep7_run (x : Builder P ι ℕ ℕ Unit) (k : Unit → Stmt P ι ℕ ℕ) : Stmt P ι ℕ ℕ :=
  @ContT.run (Stmt P ι ℕ ℕ) Id Unit x k

/-- A builder that keeps buffer `b` and costs at most `c T(m)`, through every continuation. -/
private def ep7_BW (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (p : P) (b m : ℕ)
    (x : Builder P ι ℕ ℕ Unit) (c : ℕ) : Prop :=
  ∀ (k : Unit → Stmt P ι ℕ ℕ) (c' : ℕ) V₀ Q, ep7_HT I T p b m V₀ (k ()) c' Q →
    ep7_HT I T p b m V₀ (ep7_run x k) (c + c') Q

/-- The buffer an instruction writes. -/
private def ep7_dst : Instr P ℕ ℕ → ℕ
  | .lit _ d _ => d.buf
  | .litIdx _ d _ => d.buf
  | .bin _ _ d _ _ => d.buf
  | .un _ _ d _ => d.buf
  | .copy _ d _ => d.buf
  | .draw _ _ d => d.buf
  | .convert _ _ d _ => d.buf

variable {I : Interp P ι K (OpCount P ι)} {T : ℕ → ℕ} {p : P} {b m : ℕ}

omit [DecidableEq P] in
private theorem ep7_wt_add (T : ℕ → ℕ) (c : OpCount P ι) (κ : OpKind P ι) :
    Finsupp.weight (ep7_wt T) (c + Finsupp.single κ 1) =
      Finsupp.weight (ep7_wt T) c + ep7_wt T κ := by
  rw [map_add, Finsupp.weight_single, one_smul]

private theorem ep7_size {s : Stmt P ι ℕ ℕ} {st st' : St P K (OpCount P ι)}
    (h : exec I s st = some st') : st'.store.size = st.store.size :=
  Store.size_eq_of_shape_eq (shape_eq_of_exec_eq_some h)

private theorem ep7_ht_mono {V₀ : ℕ → Option K} {s : Stmt P ι ℕ ℕ} {c c' m' : ℕ}
    {Q Q' : (ℕ → Option K) → Prop} (h : ep7_HT I T p b m V₀ s c Q) (hc : c ≤ c')
    (hm : m ≤ m') (hQ : ∀ V, Q V → Q' V) : ep7_HT I T p b m' V₀ s c' Q' := by
  intro hT hch st st' hb hV hex
  obtain ⟨h1, h2⟩ := h hT hch st st' hb hV hex
  exact ⟨h1.trans (Nat.add_le_add_left (Nat.mul_le_mul hc (hT hm)) _), hQ _ h2⟩

private theorem ep7_ht_skip {V₀ : ℕ → Option K} {Q : (ℕ → Option K) → Prop} (hQ : Q V₀) :
    ep7_HT I T p b m V₀ .skip 0 Q := by
  intro _ _ st st' _ hV hex
  rw [exec_skip] at hex
  cases hex
  exact ⟨by omega, hV ▸ hQ⟩

private theorem ep7_ht_seq {V₀ : ℕ → Option K} {s t : Stmt P ι ℕ ℕ} {c₁ c₂ : ℕ}
    {Q₁ Q : (ℕ → Option K) → Prop} (h₁ : ep7_HT I T p b m V₀ s c₁ Q₁)
    (h₂ : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ t c₂ Q) :
    ep7_HT I T p b m V₀ (.seq s t) (c₁ + c₂) Q := by
  intro hT hch st st' hb hV hex
  rw [exec_seq] at hex
  obtain ⟨st₁, hs, ht⟩ := Option.bind_eq_some_iff.mp hex
  obtain ⟨a1, a2⟩ := h₁ hT hch st st₁ hb hV hs
  obtain ⟨b1, b2⟩ := h₂ _ a2 hT hch st₁ st' (by rw [ep7_size hs]; exact hb) rfl ht
  refine ⟨?_, b2⟩
  rw [add_mul]
  omega

private theorem ep7_ht_alloc {V₀ : ℕ → Option K} {q : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {c : ℕ} {Q : (ℕ → Option K) → Prop} (h : ∀ h, b < h → ep7_HT I T p b m V₀ (body h) c Q) :
    ep7_HT I T p b m V₀ (.alloc q len body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_alloc] at hex
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hex
  have hs₂ := ep7_size h₂
  simp only [Array.size_push] at hs₂
  obtain ⟨a1, a2⟩ := h st.store.size hb hT hch _ st₂ (by simp; omega)
    (by rw [← hV]; funext i; exact Store.read_push_of_lt hb) h₂
  refine ⟨a1, ?_⟩
  have : ep7_V (Array.pop st₂.store) p b = ep7_V st₂.store p b := by
    funext i; exact Store.read_pop_of_lt (by omega)
  simpa [this] using a2

private theorem ep7_ht_named {V₀ : ℕ → Option K} {nm : String} {args : List (Arg ℕ ℕ)}
    {body : Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : ep7_HT I T p b m V₀ body c Q) : ep7_HT I T p b m V₀ (.named nm args body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_named] at hex
  exact h hT hch st st' hb hV hex

private theorem ep7_ht_ite {V₀ : ℕ → Option K} {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ}
    {t e : Stmt P ι ℕ ℕ} {c₁ c₂ : ℕ} {Q : (ℕ → Option K) → Prop}
    (ht : ep7_HT I T p b m V₀ t c₁ Q) (he : ep7_HT I T p b m V₀ e c₂ Q) :
    ep7_HT I T p b m V₀ (.ite q cmp x y t e) (c₁ + c₂) Q := by
  intro hT hch st st' hb hV hex
  rw [exec_ite] at hex
  obtain ⟨r, hr, hex⟩ := Option.bind_eq_some_iff.mp hex
  unfold cmpStep at hr
  obtain ⟨a, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨a', -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp hr
  have hw : Finsupp.weight (ep7_wt T) (st.cnt + I.charge (.cmp q)) =
      Finsupp.weight (ep7_wt T) st.cnt := by
    rw [hch, ep7_wt_add]; rfl
  split_ifs at hex
  · obtain ⟨a1, a2⟩ := ht hT hch { st with cnt := st.cnt + I.charge (.cmp q) } st' hb hV hex
    refine ⟨?_, a2⟩
    rw [hw] at a1; rw [add_mul]; omega
  · obtain ⟨a1, a2⟩ := he hT hch { st with cnt := st.cnt + I.charge (.cmp q) } st' hb hV hex
    refine ⟨?_, a2⟩
    rw [hw] at a1; rw [add_mul]; omega

private theorem ep7_ht_bindIdx {V₀ : ℕ → Option K} {q : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : ∀ v ≤ bound.eval, ep7_HT I T p b m V₀ (body v) c Q) :
    ep7_HT I T p b m V₀ (.bindIdx q x bound body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_bindIdx] at hex
  obtain ⟨r, hr, hex⟩ := Option.bind_eq_some_iff.mp hex
  unfold toNatStep at hr
  obtain ⟨a, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp hr
  dsimp only at hex
  split_ifs at hex with hle
  obtain ⟨a1, a2⟩ := h _ hle hT hch { st with cnt := st.cnt + I.charge (.toNat q) } st' hb hV hex
  refine ⟨?_, a2⟩
  rw [hch, ep7_wt_add] at a1
  exact a1

/-- the value a binder reads from cell `i` of the tracked buffer -/
private def ep7_f (I : Interp P ι K (OpCount P ι)) (p : P) (V : ℕ → Option K) (i : ℕ) : ℕ :=
  ((V i).bind (I.sem.toNat p)).getD 0

private theorem ep7_ht_bindIdx_read {V₀ : ℕ → Option K} {e : IExp ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : ep7_HT I T p b m V₀ (body (min (ep7_f I p V₀ e.eval) bound.eval)) c Q) :
    ep7_HT I T p b m V₀ (.bindIdx p ⟨b, e⟩ bound body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_bindIdx] at hex
  obtain ⟨r, hr, hex⟩ := Option.bind_eq_some_iff.mp hex
  unfold toNatStep at hr
  obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hr
  have hf : ep7_f I p V₀ e.eval = r' := by
    rw [← hV]; simp only [ep7_f, ep7_V]; rw [ha]; simp [hr']
  dsimp only at hex
  split_ifs at hex with hle
  rw [← min_eq_left hle, ← hf] at hex
  obtain ⟨a1, a2⟩ := h hT hch { st with cnt := st.cnt + I.charge (.toNat p) } st' hb hV hex
  refine ⟨?_, a2⟩
  rw [hch, ep7_wt_add] at a1
  exact a1

private theorem ep7_ht_loop0 {V₀ : ℕ → Option K} {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {Q : (ℕ → Option K) → Prop} (hn : n.eval = 0) (hQ : Q V₀) :
    ep7_HT I T p b m V₀ (.loop n body) 0 Q := by
  intro _ _ st st' _ hV hex
  rw [exec_loop, hn] at hex
  simp only [List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at hex
  subst hex
  exact ⟨by omega, hV ▸ hQ⟩

private theorem ep7_ht_loop1 {V₀ : ℕ → Option K} {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ}
    {Q : (ℕ → Option K) → Prop} (hn : n.eval = 1) (h : ep7_HT I T p b m V₀ (body 0) c Q) :
    ep7_HT I T p b m V₀ (.loop n body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_loop, hn] at hex
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil] at hex
  obtain ⟨s, hs, hex⟩ := Option.bind_eq_some_iff.mp hex
  simp only [Option.pure_def, Option.some.injEq] at hex
  subst hex
  exact h hT hch st s hb hV hs

private theorem ep7_ht_litIdx {V₀ : ℕ → Option K} {e m' : IExp ℕ} :
    ep7_HT I T p b m V₀ (.instr (.litIdx p ⟨b, e⟩ m')) 0
      (· = Function.update V₀ e.eval (I.sem.lit p (m'.eval : ℚ))) := by
  intro _ hch st st' _ hV hex
  rw [exec_instr] at hex
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hex
  simp only [Instr.run] at hr
  obtain ⟨v, hv, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp hr
  refine ⟨?_, ?_⟩
  · rw [hch, ep7_wt_add]; simp [ep7_wt, Instr.kind]
  · rw [← hV, hv]
    funext i
    simp only [ep7_V]
    by_cases hi : i = e.eval
    · subst hi; rw [Function.update_self]; exact Store.read_of_write_eq_some hw
    · rw [Function.update_of_ne hi]; exact Store.read_of_write_eq_some_of_ne hw (Or.inr hi)


private theorem ep7_run_write {sem : ScalarSem P K} {tape : Dist → ℕ → K} {s : Store P K}
    {pos : Dist → ℕ} {r : Store P K × (Dist → ℕ)} (i : Instr P ℕ ℕ)
    (h : i.run sem tape s pos = some r) :
    ∃ q j v, s.write q (ep7_dst i) j v = some r.1 := by
  cases i with
  | lit p' d q' =>
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | litIdx p' d e =>
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | bin p' o d x y =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a', -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | un p' o d x =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | copy p' d x =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | draw p' dd d =>
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | convert p' q' d x =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩

omit [DecidableEq P] in
private theorem ep7_wt_kind (i : Instr P ℕ ℕ) : ep7_wt (ι := ι) T i.kind = 0 := by
  cases i <;> rfl

private theorem ep7_sf_instr {i : Instr P ℕ ℕ} (hi : ep7_dst i ≠ b) :
    ep7_SF I T p b m (.instr i) 0 := by
  intro V₀ _ hch st st' hb hV hex
  rw [exec_instr] at hex
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hex
  obtain ⟨q, j, v, hw⟩ := ep7_run_write i hr
  refine ⟨?_, ?_⟩
  · rw [hch, ep7_wt_add, ep7_wt_kind]; omega
  · rw [← hV]; funext i'
    exact Store.read_of_write_eq_some_of_ne hw (Or.inl (Ne.symm hi))

private theorem ep7_foldr_max_le {l : List ℕ} (h : ∀ x ∈ l, x ≤ m) : l.foldr max 0 ≤ m := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

private theorem ep7_mem_kcallBlocks {outs : List (ℕ × ℕ)} {lens : List ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ kcallBlocks outs lens) : ∃ y ∈ outs, x.1 = y.1 := by
  induction outs generalizing lens with
  | nil => simp [kcallBlocks] at hx
  | cons y outs ih =>
    cases lens with
    | nil => simp [kcallBlocks] at hx
    | cons l lens =>
      simp only [kcallBlocks, List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨y, by simp, rfl⟩
      · obtain ⟨y', hy', h⟩ := ih hx
        exact ⟨y', by simp [hy'], h⟩

private theorem ep7_sf_kcall {o : ι} {q : P} {dims : List (IExp ℕ)} {ins outs : List (ℕ × IExp ℕ)}
    (ho : ∀ x ∈ outs, x.1 ≠ b) (hd : ∀ d ∈ dims, d.eval ≤ m) :
    ep7_SF I T p b m (.kcall o q dims ins outs) 1 := by
  intro V₀ hT hch st st' hb hV hex
  simp only [exec] at hex
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hex
  unfold Interp.kcallStore at hs
  split_ifs at hs with hcond
  obtain ⟨xs, -, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨ys, -, hs⟩ := Option.bind_eq_some_iff.mp hs
  refine ⟨?_, ?_⟩
  · rw [hch, ep7_wt_add]
    simp only [ep7_wt, one_mul]
    refine Nat.add_le_add_left (hT (ep7_foldr_max_le ?_)) _
    intro x hx
    obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hx
    exact hd d hdm
  · rw [← hV]; funext i'
    refine Store.read_of_writeBlocks_eq_some_of_forall hs fun x hx => Or.inl ?_
    obtain ⟨y, hy, hxy⟩ := ep7_mem_kcallBlocks hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    rw [hxy]; exact Ne.symm (ho z hz)

private theorem ep7_sf_loop {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ}
    (h : ∀ i, ep7_SF I T p b m (body i) c) : ep7_SF I T p b m (.loop n body) (n.eval * c) := by
  intro V₀ hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun i s => b < s.store.size ∧ ep7_V s.store p b = V₀ ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt + i * c * T m)
    ⟨hb, hV, by simp⟩ (fun i _ s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      obtain ⟨a1, a2⟩ := h i V₀ hT hch s₁ s₂ h1 h2 hs
      refine ⟨by rw [ep7_size hs]; exact h1, a2, ?_⟩
      rw [add_mul, add_mul, one_mul]; omega) hex
  obtain ⟨-, h2, h3⟩ := this
  exact ⟨h3, h2⟩

private theorem ep7_sf_skip : ep7_SF I T p b m .skip 0 := fun _ => ep7_ht_skip rfl

/-! Builder rules -/

private theorem ep7_bw_mono {x : Builder P ι ℕ ℕ Unit} {c c' : ℕ} (h : ep7_BW I T p b m x c)
    (hc : c ≤ c') : ep7_BW I T p b m x c' :=
  fun k c'' V₀ Q hk => ep7_ht_mono (h k c'' V₀ Q hk) (by omega) le_rfl fun _ h => h

private theorem ep7_bw_pure : ep7_BW I T p b m (pure () : Builder P ι ℕ ℕ Unit) 0 :=
  fun _ _ _ _ hk => ep7_ht_mono hk (by omega) le_rfl fun _ h => h

private theorem ep7_bw_bind {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    (hx : ep7_BW I T p b m x c₁) (hf : ep7_BW I T p b m (f ()) c₂) :
    ep7_BW I T p b m (x >>= f) (c₁ + c₂) := fun k c' V₀ Q hk =>
  ep7_ht_mono (hx (fun a => ep7_run (f a) k) (c₂ + c') V₀ Q (hf k c' V₀ Q hk)) (by omega)
    le_rfl fun _ h => h

private theorem ep7_ht_seq_sf {V₀ : ℕ → Option K} {s t : Stmt P ι ℕ ℕ} {c₁ c₂ : ℕ}
    {Q : (ℕ → Option K) → Prop} (h₁ : ep7_SF I T p b m s c₁) (h₂ : ep7_HT I T p b m V₀ t c₂ Q) :
    ep7_HT I T p b m V₀ (.seq s t) (c₁ + c₂) Q :=
  ep7_ht_seq (h₁ V₀) fun _ h => by subst h; exact h₂

private theorem ep7_bw_stmt {s : Stmt P ι ℕ ℕ} {c : ℕ} (h : ep7_SF I T p b m s c) :
    ep7_BW I T p b m (stmt s) c := fun _ _ _ _ hk => ep7_ht_seq_sf h hk

private theorem ep7_bw_ins {i : Instr P ℕ ℕ} (hi : ep7_dst i ≠ b) : ep7_BW I T p b m (ins i) 0 :=
  ep7_bw_stmt (ep7_sf_instr hi)

private theorem ep7_bw_kcall {o : ι} {q : P} {dims : List (IExp ℕ)} {ins outs : List (ℕ × IExp ℕ)}
    (ho : ∀ x ∈ outs, x.1 ≠ b) (hd : ∀ d ∈ dims, d.eval ≤ m) :
    ep7_BW I T p b m (stmt (.kcall o q dims ins outs)) 1 :=
  ep7_bw_stmt (ep7_sf_kcall ho hd)

private theorem ep7_sf_run {x : Builder P ι ℕ ℕ Unit} {c : ℕ} (h : ep7_BW I T p b m x c) :
    ep7_SF I T p b m x.run c := fun V₀ =>
  ep7_ht_mono (h (fun _ => .skip) 0 V₀ _ (ep7_ht_skip (Q := (· = V₀)) rfl)) (by omega) le_rfl
    fun _ h => h

private theorem ep7_bw_allocBind {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ h, b < h → ep7_BW I T p b m (f h) c) :
    ep7_BW I T p b m (alloc q len >>= f) c := fun k c' V₀ Q hk =>
  ep7_ht_alloc fun h' hh => h h' hh k c' V₀ Q hk

private theorem ep7_bw_forRange {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ i, ep7_BW I T p b m (body i) c) : ep7_BW I T p b m (forRange n body) (n.eval * c) :=
  fun _ _ _ _ hk => ep7_ht_seq_sf (ep7_sf_loop fun i => ep7_sf_run (h i)) hk

private theorem ep7_bw_scope {x : Builder P ι ℕ ℕ Unit} {c : ℕ} (h : ep7_BW I T p b m x c) :
    ep7_BW I T p b m (scope x) c := fun _ _ _ _ hk => ep7_ht_seq_sf (ep7_sf_run h) hk

private theorem ep7_bw_named {nm : String} {args : List (Arg ℕ ℕ)} {x : Builder P ι ℕ ℕ Unit}
    {c : ℕ}
    (h : ep7_BW I T p b m x c) : ep7_BW I T p b m (named nm args x) c :=
  fun _ _ _ _ hk => ep7_ht_seq_sf (fun V₀ => ep7_ht_named (ep7_sf_run h V₀)) hk

private theorem ep7_bw_ite {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ} {t e : Builder P ι ℕ ℕ Unit}
    {c₁ c₂ : ℕ} (ht : ep7_BW I T p b m t c₁) (he : ep7_BW I T p b m e c₂) :
    ep7_BW I T p b m (ifThenElse q cmp x y t e) (c₁ + c₂) := fun _ _ _ _ hk =>
  ep7_ht_seq_sf (fun V₀ => ep7_ht_ite (ep7_sf_run ht V₀) (ep7_sf_run he V₀)) hk

private theorem ep7_bw_bindIdx {q : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ v ≤ bound.eval, ep7_BW I T p b m (body v) c) :
    ep7_BW I T p b m (bindIdx q x bound body) c := fun _ _ _ _ hk =>
  ep7_ht_seq_sf (fun V₀ => ep7_ht_bindIdx fun v hv => ep7_sf_run (h v hv) V₀) hk

private theorem ep7_bw_when {e : IExp ℕ} {body : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ep7_BW I T p b m body c) : ep7_BW I T p b m (eighWhen e body) c := by
  unfold eighWhen
  refine ep7_bw_mono (ep7_bw_forRange fun _ => h) ?_
  simp only [IExp.eval_sub, IExp.eval_ofNat]
  exact (Nat.mul_le_mul_right c (show 1 - (1 - e.eval) ≤ 1 by omega)).trans (by simp)


private theorem ep7_bw_bind0 {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    (hx : ep7_BW I T p b m x 0) (hf : ep7_BW I T p b m (f ()) 0) :
    ep7_BW I T p b m (x >>= f) 0 := ep7_bw_bind hx hf

private theorem ep7_bw_forRange0 {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit}
    (h : ∀ i, ep7_BW I T p b m (body i) 0) : ep7_BW I T p b m (forRange n body) 0 :=
  ep7_bw_mono (ep7_bw_forRange h) (by simp)

private theorem ep7_bw_ite0 {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ} {t e : Builder P ι ℕ ℕ Unit}
    (ht : ep7_BW I T p b m t 0) (he : ep7_BW I T p b m e 0) :
    ep7_BW I T p b m (ifThenElse q cmp x y t e) 0 := ep7_bw_ite ht he

local macro "ep7_side" : tactic => `(tactic| (simp only [ep7_dst, List.mem_cons, List.mem_singleton,
  forall_eq_or_imp, forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
  IExp.eval_var, IExp.eval_add, IExp.eval_sub, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
  ne_eq, false_or, or_false, false_implies, forall_const, true_and] at * <;> omega))

local macro "ep7_z" : tactic => `(tactic| repeat (first
  | exact ep7_bw_pure
  | (apply ep7_bw_ins; ep7_side)
  | (apply ep7_bw_forRange0; intro _)
  | apply ep7_bw_scope
  | apply ep7_bw_named
  | apply ep7_bw_ite0
  | (apply ep7_bw_bindIdx; intro _ _)
  | apply ep7_bw_when
  | (apply ep7_bw_allocBind; intro _ _)
  | apply ep7_bw_bind0))

private theorem ep7_bw_zmirror {q : P} {n : IExp ℕ} {Y : ℕ} {yo : IExp ℕ} (hY : Y ≠ b) :
    ep7_BW I T p b m (zmirror q n Y yo) 0 := by
  unfold zmirror; ep7_z

private theorem ep7_bw_zhermShift {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zhermShift q n X xo c Y yo) 0 := by
  unfold zhermShift; ep7_z

private theorem ep7_bw_zhermScale {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zhermScale q n X xo c Y yo) 0 := by
  unfold zhermScale; ep7_z

private theorem ep7_bw_zhermAvg {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zhermAvg q n X xo c Y yo) 0 := by
  unfold zhermAvg; ep7_z

private theorem ep7_bw_zcopy {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zcopy q n n' X xo Y yo) 0 := by
  unfold zcopy; ep7_z

private theorem ep7_bw_zneg {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zneg q n n' X xo Y yo) 0 := by
  unfold zneg; ep7_z

private theorem ep7_bw_zconjTranspose {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zconjTranspose q n n' X xo Y yo) 0 := by
  unfold zconjTranspose; ep7_z

private theorem ep7_bw_zidentity {q : P} {n : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : ep7_BW I T p b m (zidentity q n Y yo) 0 := by
  unfold zidentity; ep7_z

private theorem ep7_bw_ztraceRe {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {d : Cell ℕ ℕ}
    (hd : d.buf ≠ b) : ep7_BW I T p b m (ztraceRe q n X xo d) 0 := by
  unfold ztraceRe; ep7_z

private theorem ep7_bw_zboxTest {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {lo hi fl : Cell ℕ ℕ}
    (hd : fl.buf ≠ b) : ep7_BW I T p b m (zboxTest q n n' X xo lo hi fl) 0 := by
  unfold zboxTest; ep7_z


local macro "ep7_k" : tactic => `(tactic| first
  | (with_reducible apply ep7_bw_zhermShift); ep7_side
  | (with_reducible apply ep7_bw_zhermScale); ep7_side
  | (with_reducible apply ep7_bw_zhermAvg); ep7_side
  | (with_reducible apply ep7_bw_zcopy); ep7_side
  | (with_reducible apply ep7_bw_zneg); ep7_side
  | (with_reducible apply ep7_bw_zconjTranspose); ep7_side
  | (with_reducible apply ep7_bw_zidentity); ep7_side
  | (with_reducible apply ep7_bw_ztraceRe); ep7_side
  | (with_reducible apply ep7_bw_zboxTest); ep7_side)

local macro "ep7_bw_tac" : tactic => `(tactic| repeat (first
  | (with_reducible exact ep7_bw_pure)
  | (with_reducible apply ep7_bw_ins); ep7_side
  | (with_reducible apply ep7_bw_kcall) <;> ep7_side
  | ep7_k
  | (with_reducible apply ep7_bw_forRange0); intro _; ep7_z; done
  | (with_reducible apply ep7_bw_forRange); intro _
  | (with_reducible apply ep7_bw_scope)
  | (with_reducible apply ep7_bw_named)
  | (with_reducible apply ep7_bw_ite)
  | (with_reducible apply ep7_bw_bindIdx); intro _ _
  | (with_reducible apply ep7_bw_when)
  | (with_reducible apply ep7_bw_allocBind); intro _ _
  | (with_reducible apply ep7_bw_bind)))

private theorem ep7_bw_nsTest {q : P} {mm : ι} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {W V : ℕ}
    {one lo hi fl : Cell ℕ ℕ} (hW : W ≠ b) (hV : V ≠ b) (hfl : fl.buf ≠ b) (hn : n.eval ≤ m) :
    ep7_BW I T p b m (newtonSchulzTestBlock q mm n X xo W V one lo hi fl) 1 := by
  unfold newtonSchulzTestBlock
  apply ep7_bw_mono
  · ep7_bw_tac
  · simp

private theorem ep7_bw_nsStep {q : P} {mm : ι} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {W V : ℕ}
    {c : Cell ℕ ℕ} (hX : X ≠ b) (hW : W ≠ b) (hV : V ≠ b) (hc : c.buf ≠ b) (hn : n.eval ≤ m) :
    ep7_BW I T p b m (newtonSchulzStepBlock q mm n X xo W V c) 1 := by
  unfold newtonSchulzStepBlock
  apply ep7_bw_mono
  · ep7_bw_tac
  · simp


private theorem ep7_bw_sign {q : P} {mm : ι} {n F : IExp ℕ} {A : ℕ} {ao : IExp ℕ} {par : ℕ}
    {po : IExp ℕ} {X : ℕ} {xo : IExp ℕ} (hX : X ≠ b) (hn : n.eval ≤ m) :
    ep7_BW I T p b m (eighSignBlock q mm n F A ao par po X xo) (2 * F.eval + 1) := by
  unfold eighSignBlock
  apply ep7_bw_mono
  · repeat (first
      | (with_reducible apply ep7_bw_nsTest) <;> ep7_side
      | (with_reducible apply ep7_bw_nsStep) <;> ep7_side
      | (with_reducible exact ep7_bw_pure)
      | (with_reducible apply ep7_bw_ins); ep7_side
      | ep7_k
      | (with_reducible apply ep7_bw_forRange); intro _
      | (with_reducible apply ep7_bw_scope)
      | (with_reducible apply ep7_bw_ite)
      | (with_reducible apply ep7_bw_allocBind); intro _ _
      | (with_reducible apply ep7_bw_bind))
  · simp; omega

private theorem ep7_bw_deflate {q : P} {mm qr : ι} {n k r lo : IExp ℕ} {side : ℕ} {Sg : ℕ}
    {sq : Cell ℕ ℕ} {Pm G Y Qf Rf Qa : ℕ} {qo : IExp ℕ} (hG : G ≠ b) (hY : Y ≠ b) (hQf : Qf ≠ b)
    (hRf : Rf ≠ b) (hQa : Qa ≠ b) (hk : k.eval ≤ m) :
    ep7_BW I T p b m (eighDeflateBlock q mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo) 2 := by
  unfold eighDeflateBlock
  apply ep7_bw_mono
  · ep7_bw_tac
  · simp

private theorem ep7_bw_compress {q : P} {mm : ι} {k r : IExp ℕ} {Qa : ℕ} {qo : IExp ℕ} {Ma : ℕ}
    {mo co : IExp ℕ} {two sg : Cell ℕ ℕ} {Qh C1 C2 C3 : ℕ} (hMa : Ma ≠ b) (hQh : Qh ≠ b)
    (hC1 : C1 ≠ b) (hC2 : C2 ≠ b) (hC3 : C3 ≠ b) (hk : k.eval ≤ m) (hr : r.eval ≤ m) :
    ep7_BW I T p b m (eighCompressBlock q mm k r Qa qo Ma mo co two sg Qh C1 C2 C3) 2 := by
  unfold eighCompressBlock
  apply ep7_bw_mono
  · ep7_bw_tac
  · simp

private theorem ep7_bw_leaf {q : P} {diag : Bool} {k : IExp ℕ} {Ma : ℕ} {mo : IExp ℕ} {Ua : ℕ}
    {uo : IExp ℕ} {Ea : ℕ} {eo : IExp ℕ} {kd : Cell ℕ ℕ} (hUa : Ua ≠ b) (hEa : Ea ≠ b)
    (hkd : kd.buf ≠ b) : ep7_BW I T p b m (eighLeafBlock q diag k Ma mo Ua uo Ea eo kd) 0 := by
  unfold eighLeafBlock
  cases diag <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ep7_z

private theorem ep7_bw_clamp {q : P} {k : IExp ℕ} {x z kc : Cell ℕ ℕ} (hx : x.buf ≠ b)
    (hz : z.buf ≠ b) (hkc : kc.buf ≠ b) : ep7_BW I T p b m (eighClampBlock q k x z kc) 0 := by
  unfold eighClampBlock; ep7_z


/-! HT rules with continuations -/

section K

variable {V₀ : ℕ → Option K} {k : Unit → Stmt P ι ℕ ℕ} {Q : (ℕ → Option K) → Prop}

private theorem ep7_ht_bwBindK {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    {c₁ c₂ : ℕ}
    (hx : ep7_BW I T p b m x c₁) (hf : ep7_HT I T p b m V₀ (ep7_run (f ()) k) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (x >>= f) k) (c₁ + c₂) Q :=
  hx (fun a => ep7_run (f a) k) c₂ V₀ Q hf

private theorem ep7_ht_bwK {x : Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    (hx : ep7_BW I T p b m x c₁) (hk : ep7_HT I T p b m V₀ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run x k) (c₁ + c₂) Q :=
  hx k c₂ V₀ Q hk

private theorem ep7_ht_bindK {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ep7_HT I T p b m V₀ (ep7_run x (fun a => ep7_run (f a) k)) c Q) :
    ep7_HT I T p b m V₀ (ep7_run (x >>= f) k) c Q := h

private theorem ep7_ht_allocK {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ h, b < h → ep7_HT I T p b m V₀ (ep7_run (f h) k) c Q) :
    ep7_HT I T p b m V₀ (ep7_run (alloc q len >>= f) k) c Q :=
  ep7_ht_alloc h

private theorem ep7_ht_litK {e m' : IExp ℕ} {c : ℕ}
    (h : ep7_HT I T p b m (Function.update V₀ e.eval (I.sem.lit p (m'.eval : ℚ))) (k ()) c Q) :
    ep7_HT I T p b m V₀ (ep7_run (ins (.litIdx p ⟨b, e⟩ m')) k) c Q := by
  change ep7_HT I T p b m V₀ (.seq (.instr (.litIdx p ⟨b, e⟩ m')) (k ())) c Q
  exact ep7_ht_mono (ep7_ht_seq ep7_ht_litIdx fun _ h' => by subst h'; exact h) (by omega) le_rfl
    fun _ h => h

private theorem ep7_ht_whenK0 {e : IExp ℕ} {B : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (he : 1 - (1 - e.eval) = 0) (h : ep7_HT I T p b m V₀ (k ()) c Q) :
    ep7_HT I T p b m V₀ (ep7_run (eighWhen e B) k) c Q := by
  change ep7_HT I T p b m V₀ (.seq (.loop (1 - (1 - e)) fun _ => B.run) (k ())) c Q
  exact ep7_ht_mono (ep7_ht_seq (c₂ := c) (ep7_ht_loop0 (Q := (· = V₀)) (by simpa using he) rfl)
    fun _ h' => by rw [h']; exact h) (by omega) le_rfl fun _ h => h

private theorem ep7_ht_whenK1 {e : IExp ℕ} {B : Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    {Q₁ : (ℕ → Option K) → Prop} (he : 1 - (1 - e.eval) = 1)
    (hB : ep7_HT I T p b m V₀ B.run c₁ Q₁) (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (eighWhen e B) k) (c₁ + c₂) Q :=
  ep7_ht_seq (ep7_ht_loop1 (n := 1 - (1 - e)) (body := fun _ => B.run) (by simpa using he) hB) h

private theorem ep7_ht_scopeK {x : Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (hx : ep7_HT I T p b m V₀ x.run c₁ Q₁) (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (scope x) k) (c₁ + c₂) Q :=
  ep7_ht_seq hx h

private theorem ep7_ht_iteK {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ} {t e : Builder P ι ℕ ℕ Unit}
    {c₁ c₂ c₃ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (ht : ep7_HT I T p b m V₀ t.run c₁ Q₁) (he : ep7_HT I T p b m V₀ e.run c₂ Q₁)
    (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₃ Q) :
    ep7_HT I T p b m V₀ (ep7_run (ifThenElse q cmp x y t e) k) (c₁ + c₂ + c₃) Q :=
  ep7_ht_seq (ep7_ht_ite ht he) h

private theorem ep7_ht_bindIdxK {q : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (hb : ∀ v ≤ bound.eval, ep7_HT I T p b m V₀ (body v).run c₁ Q₁)
    (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (bindIdx q x bound body) k) (c₁ + c₂) Q :=
  ep7_ht_seq (ep7_ht_bindIdx hb) h

private theorem ep7_ht_bindIdxReadK {e : IExp ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (hb : ep7_HT I T p b m V₀ (body (min (ep7_f I p V₀ e.eval) bound.eval)).run c₁ Q₁)
    (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (bindIdx p ⟨b, e⟩ bound body) k) (c₁ + c₂) Q :=
  ep7_ht_seq (ep7_ht_bindIdx_read hb) h

private theorem ep7_ht_run {x : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ep7_HT I T p b m V₀ (ep7_run x fun _ => .skip) c Q) :
    ep7_HT I T p b m V₀ x.run c Q := h

private theorem ep7_ht_forRangeK {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    {Q₁ : (ℕ → Option K) → Prop}
    (hl : ep7_HT I T p b m V₀ (.loop n fun i => (body i).run) c₁ Q₁)
    (h : ∀ V₁, Q₁ V₁ → ep7_HT I T p b m V₁ (k ()) c₂ Q) :
    ep7_HT I T p b m V₀ (ep7_run (forRange n body) k) (c₁ + c₂) Q :=
  ep7_ht_seq hl h

private theorem ep7_ht_skipK (hQ : Q V₀) : ep7_HT I T p b m V₀ ((fun _ => Stmt.skip) ()) 0 Q :=
  ep7_ht_skip hQ

end K

/-- the child block -/
private theorem ep7_ht_child {k : IExp ℕ} {Ma : ℕ} {mo mo' : IExp ℕ} {sg kd : Cell ℕ ℕ} {e : IExp ℕ}
    {code : ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hkd : kd.buf ≠ b) :
    ep7_HT I T p b m V₀ (eighChildBlock p k Ma mo mo' sg ⟨b, e⟩ kd code).run 0
      (· = Function.update V₀ e.eval (I.sem.lit p (k.eval : ℚ))) := by
  unfold eighChildBlock
  apply ep7_ht_mono (c := 0 + (0 + 0)) _ (by omega) le_rfl fun _ h => h
  apply ep7_ht_bwBindK (ep7_bw_zhermShift hMa)
  apply ep7_ht_bindK
  apply ep7_ht_litK
  apply ep7_ht_bwK (ep7_bw_ins ?_)
  · exact ep7_ht_skipK rfl
  · exact hkd


local macro "ep7_bwx" : tactic => `(tactic| first
  | (with_reducible apply ep7_bw_deflate) <;> ep7_side
  | (with_reducible apply ep7_bw_compress) <;> ep7_side
  | (with_reducible apply ep7_bw_sign) <;> ep7_side
  | (with_reducible apply ep7_bw_leaf) <;> ep7_side
  | (with_reducible apply ep7_bw_clamp) <;> ep7_side
  | (with_reducible apply ep7_bw_ins); ep7_side
  | (with_reducible apply ep7_bw_kcall) <;> ep7_side
  | ep7_k
  | ep7_bw_tac)

local macro "ep7_ht_tac" : tactic => `(tactic| repeat (first
  | (with_reducible apply ep7_ht_allocK); intro _ _
  | (with_reducible apply ep7_ht_bindK); (with_reducible apply ep7_ht_litK)
  | (with_reducible apply ep7_ht_litK)
  | (with_reducible apply ep7_ht_bwBindK); on_goal 1 => (ep7_bwx; done)
  | (with_reducible apply ep7_ht_bwK); on_goal 1 => (ep7_bwx; done)
  | exact ep7_ht_skipK rfl))

private theorem ep7_ht_split {mm qr : ι} {n d lo k kp : IExp ℕ} {Sg Pp Pm Ma Qa Kd Kp : ℕ}
    {two sg nsg sq : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hQa : Qa ≠ b)
    (hKd : Kd ≠ b) (hKp : Kp ≠ b) (hk : k.eval ≤ m) (hkp : kp.eval ≤ k.eval) :
    ep7_HT I T p b m V₀
      (eighSplitBlock p mm qr n d lo k kp Sg Pp Pm Ma Qa b Kd Kp two sg nsg sq).run 8
      (· = Function.update (Function.update V₀ (eighSlotOff n (d + 1) lo).eval
        (I.sem.lit p (kp.eval : ℚ))) (eighSlotOff n (d + 1) (lo + kp)).eval
        (I.sem.lit p ((k - kp).eval : ℚ))) := by
  unfold eighSplitBlock
  apply ep7_ht_run
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply ep7_ht_scopeK
    · apply ep7_ht_run
      dsimp only
      ep7_ht_tac
    · intro V h; exact ep7_ht_skipK h.symm
  · norm_num


/-- the effect of a node step on the size cells -/
private def ep7_RN (I : Interp P ι K (OpCount P ι)) (p : P) (V₀ : ℕ → Option K) (i₀ k : ℕ)
    (V : ℕ → Option K) : Prop :=
  ∃ kp ≤ k, ((kp = 0 ∨ kp = k) ∧ V = Function.update V₀ i₀ (I.sem.lit p (k : ℚ))) ∨
    (0 < kp ∧ kp < k ∧ V = Function.update (Function.update V₀ i₀ (I.sem.lit p (kp : ℚ)))
      (i₀ + kp) (I.sem.lit p ((k - kp : ℕ) : ℚ)))

private theorem ep7_ht_tail {mm qr : ι} {n d lo k : IExp ℕ} {Sg Pp Pm Ma Qa Kd Kp : ℕ}
    {two sg nsg sqh : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hQa : Qa ≠ b)
    (hKd : Kd ≠ b) (hKp : Kp ≠ b) (hk2 : 2 ≤ k.eval) (hkm : k.eval ≤ m) (v : ℕ)
    (hv : v ≤ k.eval) :
    ep7_HT I T p b m V₀ (do
        eighWhen (1 - (k - IExp.var v))
          (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) sg
            ⟨b, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 2)
        eighWhen (1 - IExp.var v)
          (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) nsg
            ⟨b, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 3)
        eighWhen (IExp.var v * (k - IExp.var v))
          (eighSplitBlock p mm qr n d lo k (IExp.var v) Sg Pp Pm Ma Qa b Kd Kp two sg nsg sqh)
        : Builder P ι ℕ ℕ Unit).run 8
      (ep7_RN I p V₀ (eighSlotOff n (d + 1) lo).eval k.eval) := by
  apply ep7_ht_run
  apply ep7_ht_bindK
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · -- the negative child
    apply ep7_ht_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_bindK
    apply ep7_ht_whenK1 (by simp) (ep7_ht_child hMa (by simpa using hKd))
    intro V₁ h₁
    apply ep7_ht_whenK0 (by simp)
    apply ep7_ht_skipK
    exact ⟨0, by omega, Or.inl ⟨Or.inl rfl, h₁⟩⟩
  rcases Nat.lt_or_ge v k.eval with hvk | hvk
  · -- a split
    apply ep7_ht_mono (c := 8 + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_bindK
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_whenK1 (by simp; have := Nat.mul_pos hv0 (Nat.sub_pos_of_lt hvk); omega)
      (ep7_ht_split hMa hQa hKd hKp hkm (by simp; omega))
    intro V₁ h₁
    apply ep7_ht_skipK
    refine ⟨v, by omega, Or.inr ⟨hv0, hvk, ?_⟩⟩
    rw [h₁]
    simp [eighSlotOff, Nat.add_assoc]
  · -- the positive child
    have hvk' : v = k.eval := by omega
    subst hvk'
    apply ep7_ht_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK1 (by simp) (ep7_ht_child hMa (by simpa using hKd))
    intro V₁ h₁
    apply ep7_ht_bindK
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_whenK0 (by simp)
    apply ep7_ht_skipK
    exact ⟨k.eval, le_rfl, Or.inl ⟨Or.inr rfl, h₁⟩⟩


private theorem ep7_ht_node {mm qr : ι} {n L F d lo k : IExp ℕ} {par Lv Su Sg Ma Qa Kd Kp : ℕ}
    {one two half negone sqh : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hQa : Qa ≠ b)
    (hKd : Kd ≠ b) (hKp : Kp ≠ b) (hk2 : 2 ≤ k.eval) (hkm : k.eval ≤ m) :
    ep7_HT I T p b m V₀ (eighNodeBlock p mm qr n L F d lo k par Lv Su Sg Ma Qa b Kd Kp one two
      half negone sqh).run (2 * F.eval + 9)
      (ep7_RN I p V₀ (eighSlotOff n (d + 1) lo).eval k.eval) := by
  unfold eighNodeBlock
  apply ep7_ht_run
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply ep7_ht_scopeK
    · apply ep7_ht_run
      dsimp only
      ep7_ht_tac
      exact ep7_ht_bindIdxK (fun v hv => ep7_ht_tail hMa hQa hKd hKp hk2 hkm v hv)
        fun V h => ep7_ht_skipK h
    · intro V h; exact ep7_ht_skipK h
  · simp only [Nat.add_zero, Nat.zero_add]
    omega

/-- the body of a slot of a downward level, at the size `k` it reads -/
private def ep7_downSlot (p : P) (mm qr : ι) (n L F d : IExp ℕ)
    (par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp t : ℕ)
    (one two half negone sqh : Cell ℕ ℕ) (lo k : ℕ) : Builder P ι ℕ ℕ Unit :=
  eighWhen (IExp.var k) do
    eighWhen (1 - (IExp.var k - 1))
      (eighLeafBlock p true (IExp.var k) Ma (eighBlockOff n d (IExp.var lo)) Ua
        (eighBlockOff n d (IExp.var lo)) Ea (eighSlotOff n d (IExp.var lo))
        ⟨Kd, eighSlotOff n d (IExp.var lo)⟩)
    eighWhen (IExp.var k - 1) do
      ins (.bin p .mul ⟨t, 4⟩ ⟨Lv, 2 * d + 1⟩ ⟨par, 0⟩)
      ifThenElse p .le ⟨Lv, 2 * d⟩ ⟨t, 4⟩
        (eighLeafBlock p false (IExp.var k) Ma (eighBlockOff n d (IExp.var lo)) Ua
          (eighBlockOff n d (IExp.var lo)) Ea (eighSlotOff n d (IExp.var lo))
          ⟨Kd, eighSlotOff n d (IExp.var lo)⟩)
        (eighNodeBlock p mm qr n L F d (IExp.var lo) (IExp.var k) par Lv Su Sg Ma Qa Sz Kd Kp one
          two half negone sqh)

private theorem ep7_ht_slot {mm qr : ι} {n L F d : IExp ℕ} {par Lv Su Sg Ma Ua Qa Ea Kd Kp t : ℕ}
    {one two half negone sqh : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hUa : Ua ≠ b)
    (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b) (ht : t ≠ b) (lo k : ℕ)
    (hkm : k ≤ m) :
    ep7_HT I T p b m V₀ (ep7_downSlot p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp t one two
      half negone sqh lo k).run (2 * F.eval + 9)
      (fun V => V = V₀ ∨
        (2 ≤ k ∧ ep7_RN I p V₀ (eighSlotOff n (d + 1) (IExp.var lo)).eval k V)) := by
  unfold ep7_downSlot
  apply ep7_ht_run
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · apply ep7_ht_mono (c := 0) _ (by omega) le_rfl fun _ h => h
      exact ep7_ht_whenK0 (by simp) (ep7_ht_skipK (Or.inl rfl))
    · have hk1 : k = 1 := by omega
      subst hk1
      apply ep7_ht_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
      apply ep7_ht_whenK1 (by simp) _ fun V h => ep7_ht_skipK h
      apply ep7_ht_run
      apply ep7_ht_bindK
      apply ep7_ht_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
      apply ep7_ht_whenK1 (by simp) (ep7_sf_run (ep7_bw_leaf hUa hEa (by simpa using hKd)) V₀)
      intro V₁ h₁
      apply ep7_ht_whenK0 (by simp)
      exact ep7_ht_skipK (Or.inl h₁)
  · apply ep7_ht_mono (c := (2 * F.eval + 9) + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK1 (by simp; omega) _ fun V h => ep7_ht_skipK h
    apply ep7_ht_run
    apply ep7_ht_bindK
    apply ep7_ht_whenK0 (by simp; omega)
    apply ep7_ht_mono (c := (2 * F.eval + 9) + 0) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_whenK1 (by simp; omega) _ fun V h => ep7_ht_skipK h
    apply ep7_ht_run
    apply ep7_ht_mono (c := 0 + (0 + (2 * F.eval + 9) + 0)) _ (by omega) le_rfl fun _ h => h
    apply ep7_ht_bwBindK (ep7_bw_ins (by simpa [ep7_dst] using ht))
    apply ep7_ht_iteK (Q₁ := fun V => V = V₀ ∨ (2 ≤ k ∧
      ep7_RN I p V₀ (eighSlotOff n (d + 1) (IExp.var lo)).eval k V))
    · exact ep7_ht_mono (ep7_sf_run (ep7_bw_leaf hUa hEa (by simpa using hKd)) V₀) le_rfl le_rfl
        fun V h => Or.inl h
    · exact ep7_ht_mono (ep7_ht_node hMa hQa hKd hKp (by simpa using hk) (by simpa using hkm))
        le_rfl le_rfl fun V h => Or.inr ⟨hk, by simpa using h⟩
    · intro V h; exact ep7_ht_skipK h


/-! Packing -/

/-- the positive entries of `g` on `[a, c)` are disjoint ranges inside `[a, c)` -/
private def ep7_Packed (g : ℕ → ℕ) (a c : ℕ) : Prop :=
  ∀ j, a ≤ j → j < c → 0 < g j → j + g j ≤ c ∧ ∀ i, j < i → i < j + g j → g i = 0

omit [DecidableEq P] in
private theorem ep7_T_zero (hTs : ∀ a b, T a + T b ≤ T (a + b)) : T 0 = 0 := by
  have := hTs 0 0; simp at this; omega

private theorem ep7_packed_sum (hT : Monotone T) (hTs : ∀ a b, T a + T b ≤ T (a + b)) {g : ℕ → ℕ}
    {c : ℕ} : ∀ a, ep7_Packed g a c → ∑ j ∈ Finset.Ico a c, T (g j) ≤ T (c - a) := by
  have hT0 := ep7_T_zero hTs
  intro a
  induction h : c - a using Nat.strong_induction_on generalizing a with
  | _ r ih =>
    intro hp
    rcases Nat.lt_or_ge a c with hac | hac
    · rcases Nat.eq_zero_or_pos (g a) with hg | hg
      · rw [Finset.sum_eq_sum_Ico_succ_bot hac, hg, hT0, zero_add]
        refine (ih (c - (a + 1)) (by omega) (a + 1) rfl fun j h1 h2 h3 =>
          hp j (by omega) h2 h3).trans (hT (by omega))
      · obtain ⟨h1, h2⟩ := hp a le_rfl hac hg
        rw [← Finset.sum_Ico_consecutive _ (show a ≤ a + g a by omega) h1,
          Finset.sum_eq_sum_Ico_succ_bot (show a < a + g a by omega)]
        have hz : ∑ j ∈ Finset.Ico (a + 1) (a + g a), T (g j) = 0 :=
          Finset.sum_eq_zero fun j hj => by
            rw [Finset.mem_Ico] at hj; rw [h2 j (by omega) (by omega), hT0]
        rw [hz, add_zero]
        have := ih (c - (a + g a)) (by omega) (a + g a) rfl fun j h1 h2 h3 => hp j (by omega) h2 h3
        calc T (g a) + ∑ j ∈ Finset.Ico (a + g a) c, T (g j) ≤ T (g a) + T (c - (a + g a)) :=
              Nat.add_le_add_left this _
          _ ≤ T (g a + (c - (a + g a))) := hTs _ _
          _ ≤ T r := hT (by omega)
    · rw [Finset.Ico_eq_empty (by omega)]; simp

private theorem ep7_packed_extend {g : ℕ → ℕ} {a c c' : ℕ} (h : ep7_Packed g a c) (hcc : c ≤ c')
    (hz : ∀ j, c ≤ j → j < c' → g j = 0) : ep7_Packed g a c' := by
  intro j h1 h2 h3
  rcases Nat.lt_or_ge j c with hj | hj
  · obtain ⟨h4, h5⟩ := h j h1 hj h3; exact ⟨by omega, h5⟩
  · rw [hz j hj h2] at h3; omega

private theorem ep7_packed_append {g : ℕ → ℕ} {a c e : ℕ} (h : ep7_Packed g a c)
    (h' : ep7_Packed g c e) (hce : c ≤ e) : ep7_Packed g a e := by
  intro j h1 h2 h3
  rcases Nat.lt_or_ge j c with hj | hj
  · obtain ⟨h4, h5⟩ := h j h1 hj h3; exact ⟨by omega, h5⟩
  · exact h' j hj h2 h3

private theorem ep7_packed_congr {g g' : ℕ → ℕ} {a c : ℕ} (h : ep7_Packed g a c)
    (he : ∀ j, a ≤ j → j < c → g' j = g j) : ep7_Packed g' a c := by
  intro j h1 h2 h3
  rw [he j h1 h2] at h3 ⊢
  obtain ⟨h4, h5⟩ := h j h1 h2 h3
  exact ⟨h4, fun i hi1 hi2 => by rw [he i (by omega) (by omega)]; exact h5 i hi1 hi2⟩

private theorem ep7_packed_zero {g : ℕ → ℕ} {a c : ℕ} (hz : ∀ j, a ≤ j → j < c → g j = 0) :
    ep7_Packed g a c := by
  intro j h1 h2 h3; rw [hz j h1 h2] at h3; omega


private theorem ep7_comb_child {g g' : ℕ → ℕ} {lo s N : ℕ} (hpk : ep7_Packed g 0 lo)
    (hz : ∀ j, lo ≤ j → j < N → g j = 0) (hs : lo + s ≤ N) (hs0 : 0 < s)
    (hg' : ∀ j, g' j = if j = lo then s else g j) :
    ep7_Packed g' 0 (lo + s) ∧ ∀ j, lo + s ≤ j → j < N → g' j = 0 := by
  refine ⟨ep7_packed_append (ep7_packed_congr hpk fun j _ h2 => by rw [hg', if_neg (by omega)])
    ?_ (by omega), fun j h1 h2 => by rw [hg', if_neg (by omega)]; exact hz j (by omega) h2⟩
  intro j h1 h2 h3
  rcases Nat.lt_or_ge lo j with hj | hj
  · rw [hg', if_neg (by omega), hz j (by omega) (by omega)] at h3; omega
  · have : j = lo := by omega
    subst this
    rw [hg', if_pos rfl]
    refine ⟨le_rfl, fun i hi1 hi2 => ?_⟩
    rw [hg', if_neg (by omega)]; exact hz i (by omega) (by omega)

private theorem ep7_comb_split {g g' : ℕ → ℕ} {lo s kp N : ℕ} (hpk : ep7_Packed g 0 lo)
    (hz : ∀ j, lo ≤ j → j < N → g j = 0) (hs : lo + s ≤ N) (hkp0 : 0 < kp) (hkp : kp < s)
    (hg' : ∀ j, g' j = if j = lo + kp then s - kp else if j = lo then kp else g j) :
    ep7_Packed g' 0 (lo + s) ∧ ∀ j, lo + s ≤ j → j < N → g' j = 0 := by
  refine ⟨ep7_packed_append (ep7_packed_congr hpk fun j _ h2 => by
      rw [hg', if_neg (by omega), if_neg (by omega)])
    ?_ (by omega), fun j h1 h2 => by
      rw [hg', if_neg (by omega), if_neg (by omega)]; exact hz j (by omega) h2⟩
  have hzero : ∀ i, lo ≤ i → i < lo + s → i ≠ lo → i ≠ lo + kp → g' i = 0 := fun i h1 h2 h3 h4 => by
    rw [hg', if_neg h4, if_neg h3]; exact hz i h1 (by omega)
  intro j h1 h2 h3
  by_cases hj1 : j = lo
  · subst hj1
    rw [hg', if_neg (by omega), if_pos rfl]
    exact ⟨by omega, fun i hi1 hi2 => hzero i (by omega) (by omega) (by omega) (by omega)⟩
  by_cases hj2 : j = lo + kp
  · subst hj2
    rw [hg', if_pos rfl]
    exact ⟨by omega, fun i hi1 hi2 => hzero i (by omega) (by omega) (by omega) (by omega)⟩
  · rw [hzero j h1 h2 hj1 hj2] at h3; omega

omit [DecidableEq P] in
private theorem ep7_f_update {V : ℕ → Option K} {i : ℕ} {v : Option K} (j : ℕ) :
    ep7_f I p (Function.update V i v) j =
      if j = i then (v.bind (I.sem.toNat p)).getD 0 else ep7_f I p V j := by
  unfold ep7_f
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [DecidableEq P] in
private theorem ep7_lit_toNat {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {j : ℕ} (hj : j ≤ B) :
    ((I.sem.lit p (j : ℚ)).bind (I.sem.toNat p)).getD 0 = j := by
  obtain ⟨z, hz, -⟩ := hlit p j hj
  rw [hz]
  simp [IsExactIntLit.toNat_eq_of_lit_eq_some hlit htn hj hz]


/-- the invariant of the slot loop of a downward level, after the slots below `lo` -/
private def ep7_Inv (I : Interp P ι K (OpCount P ι)) (p : P) (V₀ : ℕ → Option K) (N d lo : ℕ)
    (V : ℕ → Option K) : Prop :=
  ∃ C, lo ≤ C ∧ C ≤ N ∧ (∀ i, (i < N * (d + 1) ∨ N * (d + 1) + N ≤ i) → V i = V₀ i) ∧
    ep7_Packed (fun j => ep7_f I p V (N * (d + 1) + j)) 0 C ∧
    (∀ j, C ≤ j → j < N → ep7_f I p V (N * (d + 1) + j) = 0) ∧
    (∀ j, lo ≤ j → j < C → ep7_f I p V₀ (N * d + j) = 0)

omit [DecidableEq P] in
private theorem ep7_inv_step {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {V₀ V V' : ℕ → Option K} {N d lo : ℕ} (hNB : N ≤ B)
    (hlo : lo < N) (hpk : ep7_Packed (fun j => ep7_f I p V₀ (N * d + j)) 0 N)
    (hinv : ep7_Inv I p V₀ N d lo V)
    (hQ : V' = V ∨ (2 ≤ min (ep7_f I p V (N * d + lo)) (N - lo) ∧
      ep7_RN I p V (N * (d + 1) + lo) (min (ep7_f I p V (N * d + lo)) (N - lo)) V')) :
    ep7_Inv I p V₀ N d (lo + 1) V' := by
  obtain ⟨C, hC1, hC2, hfr, hpC, hzC, hz0⟩ := hinv
  have hD : N * (d + 1) = N * d + N := Nat.mul_succ N d
  have hgs : ep7_f I p V (N * d + lo) = ep7_f I p V₀ (N * d + lo) := by
    unfold ep7_f; rw [hfr _ (Or.inl (by omega))]
  rw [hgs] at hQ
  set s := ep7_f I p V₀ (N * d + lo) with hs
  -- the slot's range at depth `d`
  have hsr : 0 < s → C = lo ∧ lo + s ≤ N ∧ ∀ j, lo < j → j < lo + s →
      ep7_f I p V₀ (N * d + j) = 0 := by
    intro hs0
    have hCl : C = lo := by
      rcases Nat.lt_or_ge lo C with h | h
      · have := hz0 lo le_rfl h; omega
      · omega
    obtain ⟨h1, h2⟩ := hpk lo (Nat.zero_le _) hlo hs0
    exact ⟨hCl, h1, h2⟩
  rcases hQ with rfl | ⟨hk2, kp, hkp, hRN⟩
  · -- no write
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · rcases Nat.lt_or_ge lo C with h | h
      · exact ⟨C, h, hC2, hfr, hpC, hzC, fun j h1 h2 => hz0 j (by omega) h2⟩
      · refine ⟨lo + 1, le_rfl, by omega, hfr, ep7_packed_extend hpC (by omega) fun j h1 h2 =>
          hzC j h1 (by omega), fun j h1 h2 => hzC j (by omega) h2, fun j h1 h2 => by omega⟩
    · obtain ⟨hCl, hsN, hsz⟩ := hsr hs0
      subst hCl
      refine ⟨C + s, by omega, hsN, hfr, ep7_packed_extend hpC (by omega) fun j h1 h2 =>
          hzC j h1 (by omega), fun j h1 h2 => hzC j (by omega) h2,
          fun j h1 h2 => hsz j (by omega) h2⟩
  · have hs0 : 0 < s := by omega
    obtain ⟨hCl, hsN, hsz⟩ := hsr hs0
    subst hCl
    have hmin : min s (N - C) = s := by omega
    rw [hmin] at hkp hRN hk2
    have hlit' : ∀ j ≤ N, ((I.sem.lit p (j : ℚ)).bind (I.sem.toNat p)).getD 0 = j :=
      fun j hj => ep7_lit_toNat hlit htn (hj.trans hNB)
    rcases hRN with ⟨-, rfl⟩ | ⟨hkp0, hkps, rfl⟩
    · obtain ⟨h1, h2⟩ := ep7_comb_child (g := fun j => ep7_f I p V (N * (d + 1) + j))
        (g' := fun j => ep7_f I p (Function.update V (N * (d + 1) + C) (I.sem.lit p (s : ℚ)))
          (N * (d + 1) + j)) hpC hzC hsN hs0 fun j => by
          simp only [ep7_f_update, hlit' s (by omega)]
          by_cases hj : j = C <;> simp [hj]
      refine ⟨C + s, by omega, hsN, fun i hi => ?_, h1, h2, fun j h1 h2 => hsz j (by omega) h2⟩
      rw [Function.update_of_ne (by omega)]; exact hfr i hi
    · obtain ⟨h1, h2⟩ := ep7_comb_split (g := fun j => ep7_f I p V (N * (d + 1) + j))
        (g' := fun j => ep7_f I p (Function.update (Function.update V (N * (d + 1) + C)
          (I.sem.lit p (kp : ℚ))) (N * (d + 1) + C + kp) (I.sem.lit p ((s - kp : ℕ) : ℚ)))
          (N * (d + 1) + j)) hpC hzC hsN hkp0 hkps fun j => by
          simp only [ep7_f_update, hlit' kp (by omega), hlit' (s - kp) (by omega)]
          by_cases hj : j = C + kp
          · simp [hj, Nat.add_assoc]
          · by_cases hj' : j = C
            · simp [hj']
            · simp [hj, hj', show ¬ (N * (d + 1) + j = N * (d + 1) + C + kp) by omega]
      refine ⟨C + s, by omega, hsN, fun i hi => ?_, h1, h2, fun j h1 h2 => hsz j (by omega) h2⟩
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hfr i hi


private theorem ep7_ht_downLoop {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {mm qr : ι} {n L F d : IExp ℕ}
    {par Lv Su Sg Ma Ua Qa Ea Kd Kp t : ℕ} {one two half negone sqh : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hUa : Ua ≠ b)
    (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b) (ht : t ≠ b) (hNB : n.eval ≤ B)
    (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * d.eval + j)) 0 n.eval)
    (hz : ∀ j, j < n.eval → ep7_f I p V₀ (n.eval * (d.eval + 1) + j) = 0) :
    ep7_HT I T p b n.eval V₀ (.loop n fun lo => (bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
      (n - IExp.var lo) fun k => ep7_downSlot p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp t
        one two half negone sqh lo k).run) (2 * F.eval + 9)
      (ep7_Inv I p V₀ n.eval d.eval n.eval) := by
  intro hT hch st st' hb hV hex
  set N := n.eval
  set c := 2 * F.eval + 9
  set g₀ : ℕ → ℕ := fun j => ep7_f I p V₀ (N * d.eval + j)
  have := forall_of_exec_loop_eq_some I (fun lo s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt +
        c * ∑ j ∈ Finset.range lo, T (g₀ j) ∧ ep7_Inv I p V₀ N d.eval lo (ep7_V s.store p b))
    ⟨hb, by simp, 0, le_rfl, Nat.zero_le _, fun i _ => by rw [hV],
      fun j _ h => absurd h (Nat.not_lt_zero _), fun j _ h => by rw [hV]; exact hz j h,
      fun j h1 h2 => absurd h2 (by omega)⟩
    (fun lo hlo s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hslot : ep7_HT I T p b (min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo))
          (ep7_V s₁.store p b) ((bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
          (n - IExp.var lo) fun k => ep7_downSlot p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp
            t one two half negone sqh lo k).run) (c + 0)
          (fun V => V = ep7_V s₁.store p b ∨
            (2 ≤ min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo) ∧
            ep7_RN I p (ep7_V s₁.store p b) (N * (d.eval + 1) + lo)
              (min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo)) V)) := by
        apply ep7_ht_run
        apply ep7_ht_bindIdxReadK _ fun V h => ep7_ht_skipK h
        have e1 : (eighSlotOff n d (IExp.var lo)).eval = N * d.eval + lo := by simp [eighSlotOff, N]
        have e2 : (eighSlotOff n (d + 1) (IExp.var lo)).eval = N * (d.eval + 1) + lo := by
          simp [eighSlotOff, N]
        have e3 : (n - IExp.var lo).eval = N - lo := by simp [N]
        rw [e1, e3]
        have := ep7_ht_slot (I := I) (T := T) (p := p) (b := b) (V₀ := ep7_V s₁.store p b)
          (mm := mm) (qr := qr) (n := n) (L := L) (F := F) (d := d) (par := par) (Lv := Lv)
          (Su := Su) (Sg := Sg) (one := one) (two := two) (half := half) (negone := negone)
          (sqh := sqh) hMa hUa hQa hEa hKd hKp ht lo
          (min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo)) le_rfl
        rw [e2] at this
        exact this
      obtain ⟨a1, a2⟩ := hslot hT hch s₁ s₂ h1 rfl hs
      rw [Nat.add_zero] at a1
      have h3' := h3
      obtain ⟨C, -, -, hfr, -⟩ := h3'
      have hg : ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo) = g₀ lo := by
        simp only [g₀, ep7_f]; rw [hfr _ (Or.inl (by rw [Nat.mul_succ]; omega))]
      refine ⟨by rw [ep7_size hs]; exact h1, ?_, ep7_inv_step hlit htn hNB hlo hpk h3 a2⟩
      rw [Finset.sum_range_succ, Nat.mul_add]
      have : T (min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo)) ≤ T (g₀ lo) :=
        hT (by rw [hg]; exact min_le_left _ _)
      have := Nat.mul_le_mul_left c this
      omega) hex
  obtain ⟨-, h2, h3⟩ := this
  refine ⟨h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left c ?_) _), h3⟩
  have := ep7_packed_sum hT hTs 0 hpk
  rwa [← Finset.range_eq_Ico, Nat.sub_zero] at this


private theorem ep7_ht_down {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {mm qr : ι} {n L F d : IExp ℕ}
    {par Lv Su Sg Ma Ua Qa Ea Kd Kp : ℕ} {one two half negone sqh : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hLv : Lv ≠ b) (hSu : Su ≠ b) (hSg : Sg ≠ b) (hMa : Ma ≠ b)
    (hUa : Ua ≠ b) (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b)
    (hNB : n.eval ≤ B) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * d.eval + j)) 0 n.eval)
    (hz : ∀ j, j < n.eval → ep7_f I p V₀ (n.eval * (d.eval + 1) + j) = 0) :
    ep7_HT I T p b n.eval V₀ (eighDownLevel p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp one
      two half negone sqh).run (2 * F.eval + 9) (ep7_Inv I p V₀ n.eval d.eval n.eval) := by
  unfold eighDownLevel
  apply ep7_ht_run
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply ep7_ht_scopeK
    · apply ep7_ht_run
      ep7_ht_tac
      exact ep7_ht_forRangeK (ep7_ht_downLoop hlit htn hMa hUa hQa hEa hKd hKp (by omega) hNB hTs
        hpk hz) fun V h => ep7_ht_skipK h
    · intro V h; exact ep7_ht_skipK h
  · simp only [Nat.add_zero, Nat.zero_add]
    omega


/-- the body of a slot of an upward level, at the size `k` it reads -/
private def ep7_upSlot (p : P) (mm : ι) (n d : IExp ℕ) (Ua Qa Ea Kd Kp t : ℕ) (lo k : ℕ) :
    Builder P ι ℕ ℕ Unit :=
  eighWhen (IExp.var k) <| bindIdx p ⟨Kd, eighSlotOff n d (IExp.var lo)⟩ 4 fun c => do
    eighWhen (eighEqInd (IExp.var c) 2) do
      zcopy p (IExp.var k) (IExp.var k) Ua (eighBlockOff n (d + 1) (IExp.var lo)) Ua
        (eighBlockOff n d (IExp.var lo))
      forRange (IExp.var k) fun i => ins (.bin p .add ⟨Ea, eighSlotOff n d (IExp.var lo) + .var i⟩
        ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + .var i⟩ ⟨t, 0⟩)
    eighWhen (eighEqInd (IExp.var c) 3) do
      zcopy p (IExp.var k) (IExp.var k) Ua (eighBlockOff n (d + 1) (IExp.var lo)) Ua
        (eighBlockOff n d (IExp.var lo))
      forRange (IExp.var k) fun i => ins (.bin p .add ⟨Ea, eighSlotOff n d (IExp.var lo) + .var i⟩
        ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + .var i⟩ ⟨t, 1⟩)
    eighWhen (eighEqInd (IExp.var c) 4) <|
      bindIdx p ⟨Kp, eighSlotOff n d (IExp.var lo)⟩ (IExp.var k) fun kp => do
        let qo := eighBlockOff n d (IExp.var lo)
        stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
          [(Qa, qo), (Ua, eighBlockOff n (d + 1) (IExp.var lo))]
          [(Ua, eighBlockOff n d (IExp.var lo))])
        stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp, IExp.var k - IExp.var kp]
          [(Qa, qo + 2 * (IExp.var k * IExp.var kp)),
            (Ua, eighBlockOff n (d + 1) (IExp.var lo + IExp.var kp))]
          [(Ua, eighBlockOff n d (IExp.var lo) + 2 * (IExp.var k * IExp.var kp))])
        forRange (IExp.var kp) fun j => ins (.bin p .add
          ⟨Ea, eighSlotOff n d (IExp.var lo) + .var j⟩
          ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + .var j⟩ ⟨t, 0⟩)
        forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
          ⟨Ea, eighSlotOff n d (IExp.var lo) + IExp.var kp + .var j⟩
          ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + IExp.var kp + .var j⟩ ⟨t, 0⟩)

private theorem ep7_bw_upSlot {mm : ι} {n d : IExp ℕ} {Ua Qa Ea Kd Kp t : ℕ} (hUa : Ua ≠ b)
    (hEa : Ea ≠ b) (lo k : ℕ) :
    ep7_BW I T p b k (ep7_upSlot p mm n d Ua Qa Ea Kd Kp t lo k) 2 := by
  unfold ep7_upSlot
  apply ep7_bw_mono
  · dsimp only
    ep7_bw_tac
  · simp


private theorem ep7_ht_upLoop {mm : ι} {n d : IExp ℕ} {Ua Qa Ea Kd Kp t : ℕ} {V₀ : ℕ → Option K}
    (hUa : Ua ≠ b) (hEa : Ea ≠ b) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * d.eval + j)) 0 n.eval) :
    ep7_HT I T p b n.eval V₀ (.loop n fun lo => (bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
      (n - IExp.var lo) fun k => ep7_upSlot p mm n d Ua Qa Ea Kd Kp t lo k).run) 2 (· = V₀) := by
  intro hT hch st st' hb hV hex
  set N := n.eval
  set g₀ : ℕ → ℕ := fun j => ep7_f I p V₀ (N * d.eval + j)
  have := forall_of_exec_loop_eq_some I (fun lo s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt +
        2 * ∑ j ∈ Finset.range lo, T (g₀ j) ∧ ep7_V s.store p b = V₀)
    ⟨hb, by simp, hV⟩
    (fun lo hlo s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hslot : ep7_HT I T p b (min (ep7_f I p V₀ (N * d.eval + lo)) (N - lo))
          V₀ ((bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
          (n - IExp.var lo) fun k => ep7_upSlot p mm n d Ua Qa Ea Kd Kp t lo k).run) (2 + 0)
          (· = V₀) := by
        apply ep7_ht_run
        apply ep7_ht_bindIdxReadK _ fun V h => ep7_ht_skipK h
        have e1 : (eighSlotOff n d (IExp.var lo)).eval = N * d.eval + lo := by simp [eighSlotOff, N]
        have e3 : (n - IExp.var lo).eval = N - lo := by simp [N]
        rw [e1, e3]
        exact ep7_sf_run (ep7_bw_upSlot hUa hEa lo _) V₀
      obtain ⟨a1, a2⟩ := hslot hT hch s₁ s₂ h1 h3 hs
      rw [Nat.add_zero] at a1
      refine ⟨by rw [ep7_size hs]; exact h1, ?_, a2⟩
      rw [Finset.sum_range_succ, Nat.mul_add]
      have : T (min (ep7_f I p V₀ (N * d.eval + lo)) (N - lo)) ≤ T (g₀ lo) :=
        hT (min_le_left _ _)
      omega) hex
  obtain ⟨-, h2, h3⟩ := this
  refine ⟨h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 ?_) _), h3⟩
  have := ep7_packed_sum hT hTs 0 hpk
  rwa [← Finset.range_eq_Ico, Nat.sub_zero] at this

private theorem ep7_ht_up {mm : ι} {n d : IExp ℕ} {Lv Ua Qa Ea Kd Kp : ℕ} {two : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hUa : Ua ≠ b) (hEa : Ea ≠ b) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * d.eval + j)) 0 n.eval) :
    ep7_HT I T p b n.eval V₀ (eighUpLevel p mm n d Lv Ua Qa Ea b Kd Kp two).run 2 (· = V₀) := by
  unfold eighUpLevel
  apply ep7_ht_run
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply ep7_ht_scopeK
    · apply ep7_ht_run
      ep7_ht_tac
      exact ep7_ht_forRangeK (ep7_ht_upLoop hUa hEa hTs hpk) fun V h => ep7_ht_skipK h
    · intro V h; exact ep7_ht_skipK h
  · simp only [Nat.add_zero, Nat.zero_add]
    omega


private theorem ep7_bw_bottom {n D : IExp ℕ} {Ua Ea : ℕ} (hUa : Ua ≠ b) (hEa : Ea ≠ b) :
    ep7_BW I T p b m (eighBottomLevel p n D Ua Ea b) 0 := by
  unfold eighBottomLevel; ep7_z

private theorem ep7_ht_zeroLoop {M : IExp ℕ} {V₀ : ℕ → Option K} :
    ep7_HT I T p b m V₀ (.loop M fun w => (ins (.litIdx p ⟨b, IExp.var w⟩ 0)).run) 0
      (fun V => ∀ w, V w = if w < M.eval then I.sem.lit p 0 else V₀ w) := by
  intro hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun i s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt ∧
      ∀ w, ep7_V s.store p b w = if w < i then I.sem.lit p 0 else V₀ w)
    ⟨hb, le_rfl, fun w => by simp [hV]⟩
    (fun i _ s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hl : ep7_HT I T p b m (ep7_V s₁.store p b)
          (.seq (.instr (.litIdx p ⟨b, IExp.var i⟩ 0)) .skip) (0 + 0)
          (· = Function.update (ep7_V s₁.store p b) (IExp.var i).eval
            (I.sem.lit p ((0 : IExp ℕ).eval : ℚ))) :=
        ep7_ht_seq ep7_ht_litIdx fun V₁ h => ep7_ht_skip h
      obtain ⟨a1, a2⟩ := hl hT hch s₁ s₂ h1 rfl hs
      refine ⟨by rw [ep7_size hs]; exact h1, by omega, fun w => ?_⟩
      rw [a2]
      by_cases hw : w = i
      · subst hw; simp
      · rw [Function.update_of_ne (by simpa using hw), h3 w]
        by_cases hwi : w < i
        · simp [hwi, show w < i + 1 by omega]
        · simp [hwi, show ¬ w < i + 1 by omega]) hex
  obtain ⟨-, h2, h3⟩ := this
  exact ⟨by omega, h3⟩


private theorem ep7_ht_downPass {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {mm qr : ι} {n L F : IExp ℕ}
    {par Lv Su Sg Ma Ua Qa Ea Kd Kp : ℕ} {one two half negone sqh : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hLv : Lv ≠ b) (hSu : Su ≠ b) (hSg : Sg ≠ b) (hMa : Ma ≠ b)
    (hUa : Ua ≠ b) (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b)
    (hNB : n.eval ≤ B) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * 0 + j)) 0 n.eval)
    (hz : ∀ e, 0 < e → e ≤ L.eval + 1 → ∀ j, j < n.eval → ep7_f I p V₀ (n.eval * e + j) = 0) :
    ep7_HT I T p b n.eval V₀ (.loop (L + 1) fun d => (eighDownLevel p mm qr n L F (IExp.var d)
      par Lv Su Sg Ma Ua Qa Ea b Kd Kp one two half negone sqh).run)
      ((L.eval + 1) * (2 * F.eval + 9))
      (fun V => ∀ e ≤ L.eval + 1, ep7_Packed (fun j => ep7_f I p V (n.eval * e + j)) 0 n.eval) := by
  intro hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun d s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤
        Finsupp.weight (ep7_wt T) st.cnt + d * ((2 * F.eval + 9) * T n.eval) ∧
      (∀ e ≤ d, ep7_Packed (fun j => ep7_f I p (ep7_V s.store p b) (n.eval * e + j)) 0 n.eval) ∧
      (∀ e, d < e → e ≤ L.eval + 1 → ∀ j, j < n.eval →
        ep7_f I p (ep7_V s.store p b) (n.eval * e + j) = 0))
    ⟨hb, by simp, fun e he => by
      rw [Nat.le_zero.mp he, hV]; exact hpk, fun e h1 h2 => by rw [hV]; exact hz e h1 h2⟩
    (fun d hd s₁ s₂ ⟨h1, h2, h3, h4⟩ hs => by
      have hdn := ep7_ht_down (I := I) (T := T) (p := p) (b := b) (mm := mm) (qr := qr) (n := n)
        (L := L) (F := F) (d := IExp.var d) (par := par) (one := one) (two := two) (half := half)
        (negone := negone) (sqh := sqh) hlit htn hLv hSu hSg hMa hUa hQa hEa hKd hKp hNB hTs
        (h3 d le_rfl) (h4 (d + 1) (by omega) (by simpa using hd))
      obtain ⟨a1, ⟨C, hC1, hC2, hfr, hpC, -, -⟩⟩ := hdn hT hch s₁ s₂ h1 rfl hs
      simp only [IExp.eval_var] at hfr hpC
      have hCN : C = n.eval := by omega
      rw [hCN] at hpC
      refine ⟨by rw [ep7_size hs]; exact h1, by rw [Nat.succ_mul]; omega, fun e he => ?_,
        fun e h5 h6 j hj => ?_⟩
      · rcases Nat.lt_or_ge d e with hde | hde
        · have : e = d + 1 := by omega
          subst this; exact hpC
        · refine ep7_packed_congr (h3 e hde) fun j _ hj => ?_
          have : n.eval * e ≤ n.eval * d := Nat.mul_le_mul_left n.eval hde
          simp only [ep7_f]; rw [hfr _ (Or.inl (by rw [Nat.mul_succ]; omega))]
      · have : n.eval * (d + 2) ≤ n.eval * e := Nat.mul_le_mul_left n.eval (by omega)
        have h7 := h4 e (by omega) h6 j hj
        have e1 : n.eval * (d + 2) = n.eval * d + n.eval + n.eval := by ring
        have e2 : n.eval * (d + 1) = n.eval * d + n.eval := by ring
        simp only [ep7_f] at h7 ⊢; rw [hfr _ (Or.inr (by omega))]
        exact h7) hex
  obtain ⟨-, h2, h3, -⟩ := this
  refine ⟨?_, h3⟩
  simp only [IExp.eval_add, IExp.eval_ofNat] at h2
  rw [Nat.mul_assoc]; exact h2

private theorem ep7_ht_upPass {mm : ι} {n L : IExp ℕ} {Lv Ua Qa Ea Kd Kp : ℕ} {two : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hUa : Ua ≠ b) (hEa : Ea ≠ b) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ∀ e ≤ L.eval, ep7_Packed (fun j => ep7_f I p V₀ (n.eval * e + j)) 0 n.eval) :
    ep7_HT I T p b n.eval V₀ (.loop (L + 1) fun d' => (eighUpLevel p mm n (L - IExp.var d') Lv Ua
      Qa Ea b Kd Kp two).run) ((L.eval + 1) * 2) (· = V₀) := by
  intro hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun d s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt + d * (2 * T n.eval) ∧
      ep7_V s.store p b = V₀)
    ⟨hb, by simp, hV⟩
    (fun d hd s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hup := ep7_ht_up (I := I) (T := T) (p := p) (b := b) (mm := mm) (n := n)
        (d := L - IExp.var d) (Lv := Lv) (Qa := Qa) (Kd := Kd) (Kp := Kp) (two := two) hUa hEa hTs
        (hpk (L - IExp.var d).eval (by simp))
      obtain ⟨a1, a2⟩ := hup hT hch s₁ s₂ h1 h3 hs
      exact ⟨by rw [ep7_size hs]; exact h1, by rw [Nat.succ_mul]; omega, a2⟩) hex
  obtain ⟨-, h2, h3⟩ := this
  refine ⟨?_, h3⟩
  simp only [IExp.eval_add, IExp.eval_ofNat] at h2
  rw [Nat.mul_assoc]; exact h2


/-- a cost bound for a run before the tracked buffer is allocated, `j` allocations ahead -/
private def ep7_HTpre (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (b m j : ℕ) (s : Stmt P ι ℕ ℕ)
    (c : ℕ) : Prop :=
  Monotone T → (∀ κ, I.charge κ = Finsupp.single κ 1) → ∀ st st' : St P K (OpCount P ι),
    st.store.size + j = b → exec I s st = some st' →
    Finsupp.weight (ep7_wt T) st'.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt + c * T m

private theorem ep7_pre_allocSucc {j : ℕ} {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit}
    {k : Unit → Stmt P ι ℕ ℕ} {c : ℕ}
    (h : ∀ h, h + (j + 1) = b → ep7_HTpre I T b m j (ep7_run (f h) k) c) :
    ep7_HTpre I T b m (j + 1) (ep7_run (alloc q len >>= f) k) c := by
  intro hT hch st st' hb hex
  change exec I (.alloc q len fun h => ep7_run (f h) k) st = some st' at hex
  rw [exec_alloc] at hex
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hex
  have := h st.store.size hb hT hch _ st₂ (by simp only [Array.size_push]; omega) h₂
  exact this

private theorem ep7_pre_allocZero {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit}
    {k : Unit → Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : ep7_HT I T p b m (fun _ => none) (ep7_run (f b) k) c Q) :
    ep7_HTpre I T b m 0 (ep7_run (alloc q len >>= f) k) c := by
  intro hT hch st st' hb hex
  change exec I (.alloc q len fun h => ep7_run (f h) k) st = some st' at hex
  rw [exec_alloc] at hex
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hex
  rw [Nat.add_zero] at hb
  subst hb
  have := (h hT hch _ st₂ (by simp) (by
    funext i; simp only [ep7_V]; rw [Store.read_push_size]
    rw [Array.getElem?_replicate]; split_ifs <;> rfl) h₂).1
  exact this

private theorem ep7_pre_scope {j : ℕ} {x : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ep7_HTpre I T b m j (ep7_run x fun _ => .skip) c) :
    ep7_HTpre I T b m j (scope x).run c := by
  intro hT hch st st' hb hex
  change exec I (.seq (ep7_run x fun _ => .skip) .skip) st = some st' at hex
  rw [exec_seq_skip] at hex
  exact h hT hch st st' hb hex


omit [DecidableEq P] in
private theorem ep7_init {dec : P → K → ℝ} (N ℓ₀ : ℕ) (hlit : IsExactIntLit dec I.sem (N + 4))
    (htn : IsExactToNat dec I.sem) {V₀ V₁ : ℕ → Option K}
    (h₁ : ∀ w, V₁ w = if w < N * (ℓ₀ + 1 + 1) + 1 then I.sem.lit p 0 else V₀ w) :
    ep7_Packed (fun j => ep7_f I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) (N * 0 + j)) 0 N ∧
      ∀ e, 0 < e → e ≤ ℓ₀ + 1 → ∀ j, j < N →
        ep7_f I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) (N * e + j) = 0 := by
  have hz : ∀ i, i ≠ 0 → i < N * (ℓ₀ + 1 + 1) + 1 →
      ep7_f I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) i = 0 := by
    intro i hi hiM
    rw [ep7_f_update, if_neg hi]
    unfold ep7_f; rw [h₁, if_pos hiM]
    exact_mod_cast ep7_lit_toNat (j := 0) hlit htn (Nat.zero_le _)
  have hbig : ∀ e ≤ ℓ₀ + 1, ∀ j < N, N * e + j < N * (ℓ₀ + 1 + 1) + 1 := by
    intro e he j hj
    have : N * e ≤ N * (ℓ₀ + 1) := Nat.mul_le_mul_left N he
    have : N * (ℓ₀ + 1 + 1) = N * (ℓ₀ + 1) + N := Nat.mul_succ _ _
    omega
  have hf0 : ep7_f I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) 0 = N := by
    rw [ep7_f_update, if_pos rfl]; exact ep7_lit_toNat hlit htn (by omega)
  have hb0 : ∀ j < N, j < N * (ℓ₀ + 1 + 1) + 1 := fun j hj => by simpa using hbig 0 (by omega) j hj
  refine ⟨fun j _ hj hpos => ?_, fun e he0 he j hj => hz _ ?_ (hbig e he j hj)⟩
  · dsimp only at hpos ⊢
    rw [Nat.mul_zero, Nat.zero_add] at hpos ⊢
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hf0]
      refine ⟨by omega, fun i hi1 hi2 => ?_⟩
      rw [Nat.zero_add]
      exact hz i (by omega) (hb0 i (by omega))
    · rw [hz j (by omega) (hb0 j hj)] at hpos
      omega
  · have : N * e ≥ N := Nat.le_mul_of_pos_right N he0
    omega

set_option maxHeartbeats 2000000 in
-- the whole program is unfolded and every block is checked in one proof
private theorem ep7_main {dec : P → K → ℝ} {mm qr : ι} (N ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (hTs : ∀ a b, T a + T b ≤ T (a + b)) (hb5 : 5 ≤ b) :
    ep7_HTpre I T b N 5 (eighProg p mm qr (.const N) (.const ℓ₀) (.const F) 0 1 2 3).run
      ((ℓ₀ + 1) * (2 * F + 9) + (ℓ₀ + 1) * 2) := by
  unfold eighProg
  apply ep7_pre_scope
  dsimp only
  apply ep7_pre_allocSucc; intro hc hhc
  apply ep7_pre_allocSucc; intro hMa hhMa
  apply ep7_pre_allocSucc; intro hUa hhUa
  apply ep7_pre_allocSucc; intro hQa hhQa
  apply ep7_pre_allocSucc; intro hEa hhEa
  apply ep7_pre_allocZero (p := p) (Q := fun _ => True)
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ _ => trivial)
  · ep7_ht_tac
    apply ep7_ht_bindK
    apply ep7_ht_forRangeK ep7_ht_zeroLoop
    · intro V₁ h₁
      apply ep7_ht_bindK
      apply ep7_ht_litK
      ep7_ht_tac
      apply ep7_ht_bindK
      obtain ⟨hpk, hz⟩ := ep7_init (I := I) (p := p) N ℓ₀ hlit htn (V₀ := fun _ => none)
        (V₁ := V₁) (by simpa using h₁)
      apply ep7_ht_forRangeK (ep7_ht_downPass hlit htn (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by simp) hTs (by simpa using hpk)
        (by simpa using hz))
      · intro V₂ h₂
        apply ep7_ht_bwK (ep7_bw_bottom (by omega) (by omega))
        · apply ep7_ht_bindK
          apply ep7_ht_forRangeK (ep7_ht_upPass (by omega) (by omega) hTs fun e he =>
            h₂ e (by simp at he ⊢; omega))
          · intro V₃ h₃
            ep7_ht_tac
            exact ep7_ht_skipK (Q := fun _ => True) trivial
  · simp only [IExp.eval_const, Nat.zero_add, Nat.add_zero]
    exact le_rfl


end EP7

/-- **The kernel cost of the registered tree, weighted** ([Shah2024, Section 4], the operation count
of Theorem 4.2): for a cost $T$ of a kernel call by its largest dimension that is monotone and
superadditive ($T(a) + T(b) \le T(a + b)$, as a convex $T$ with $T(0) = 0$ is), under the standard
charge, exact integer literals up to $N + 4$ and the exact floor conversion (the sizes, kinds and
$k_+$ are control data in rounded cells, read back by binders: without the contracts a slot that
starts no node can read back a size $\ge 1$, design note §8), every successful run of
`NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$ adds
at most $(\ell_0 + 1)(2F + 12)\,T(N)$ to the weighted kernel count: per level, the nodes have sizes
summing to at most $N$, each with at most $2F + 12$ kernel calls of largest dimension at most its
size. The static bound `NLAlib.eighCount` charges every size at every slot, a factor of about $N^2$
more. No printed source.
Proof: an invariant of the run (not of `NLAlib.Computation.FStmt.staticCost`) that tracks only the
size arena `Sz` and the weighted count: a Hoare triple for the cost and the cells of `Sz`
(`ep7_HT`), with frame rules for every block that does not write `Sz` (`ep7_BW`; no semantic
contract, the kernels are arbitrary). A node step of size $k$ makes at most $2F + 9$ kernel calls of
largest dimension at most $k$ (the sign set-up and $F$ steps, two deflations, two compressions;
$k_+ \le k$, the binder's bound) and writes only the sizes of its children, $k$ at slot $lo$ or
$k_+$ and $k - k_+$ at $lo$ and $lo + k_+$ of depth $d + 1$, read back exactly (`hlit`, `htn`,
`NLAlib.Computation.IsExactIntLit.toNat_eq_of_lit_eq_some`); so the sizes of each depth stay
*packed* (disjoint ranges inside $[0, N)$, `ep7_Packed`), and $\sum_{lo} T(k_{lo}) \le T(N)$ by
superadditivity and monotonicity (`ep7_packed_sum`). A downward level costs $(2F + 9)T(N)$, an
upward level (two calls per split) $2T(N)$, the rest nothing; over the $\ell_0 + 1$ levels of each
pass, $(\ell_0 + 1)(2F + 11)T(N)$. -/
theorem eighProg.weight_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : ∀ k, I.charge k = Finsupp.single k 1) {dec : P → K → ℝ} (p : P) (N ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem) (T : ℕ → ℕ)
    (hT : Monotone T) (hTsup : ∀ a b, T a + T b ≤ T (a + b)) {st st' : St P K (OpCount P ι)}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F] st = some st') :
    Finsupp.weight (fun κ : OpKind P ι => match κ with
        | .kcall _ _ ds => T (ds.foldr max 0)
        | _ => 0) st'.cnt ≤
      Finsupp.weight (fun κ : OpKind P ι => match κ with
        | .kcall _ _ ds => T (ds.foldr max 0)
        | _ => 0) st.cnt + (ℓ₀ + 1) * (2 * F + 12) * T N := by
  rw [Prog.exec_eq_exec_toStmt, eighProg.toStmt_compiled] at h
  have h' : exec I (eighProg p mm qr (.const N) (.const ℓ₀) (.const F) 0 1 2 3).run st =
      some st' := h
  change Finsupp.weight (ep7_wt T) st'.cnt ≤
    Finsupp.weight (ep7_wt T) st.cnt + (ℓ₀ + 1) * (2 * F + 12) * T N
  have := ep7_main (I := I) (T := T) (p := p) (b := st.store.size + 5) (mm := mm) (qr := qr)
    N ℓ₀ F hlit htn hTsup (by omega) hT hc st st' rfl h'
  refine this.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _)
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (by omega)

end NLAlib
