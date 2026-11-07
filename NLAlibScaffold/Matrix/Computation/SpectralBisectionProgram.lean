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

/-- **One level of the downward pass**: let the kernels of `I` be the routines `mmR`, `qrR` on
interleaved pairs, the semantics decide flags, with exact integer literals up to $n + 4$ and the
exact floor conversion; $M$ = `NLAlib.eighTapeMachine I p mmR qrR` and the root
$(n, \mathbf{A}, R_0, \varepsilon, \ell_0)$. A successful run of `NLAlib.eighDownLevel` at depth
$d < D$ from a state whose arenas hold the nodes of depth $d$ (`NLAlib.EighArenas.LevelHolds`), with
the tape positions $nd$ (uniform) and $4n^2 d$ (Gaussian), the stored $R_0$, $\varepsilon$, $\beta$
in `par` and the constants in `c`, ends with the arenas holding the nodes of depth $d + 1$ and the
records of depth $d$ (`NLAlib.EighArenas.RecordHolds`); every cell outside depths $d$ and $d + 1$ of
the arenas and the sample buffers `Su`, `Sg` is unchanged, the store shape too, and the tape
positions advance by $n$ and $4n^2$. No printed source.
Proof: the parameters of depth $d + 1$ by seven instructions (`NLAlib.eighNextParams` at
$\ell_0 + d$, `NLAlib.eighLevelParams`); the draws by `NLAlib.Computation.exec_forRange_draw` (cell
$i$ of `Su` is the tape at $nd + i$, cell $w$ of `Sg` at $4n^2 d + w$); then the loop over the slots
by `NLAlib.Computation.forall_of_exec_loop_eq_some` (pilot) with the invariant "the slots below $lo$
are done": at slot $lo$ the binder reads the stored size (`hlev`, `NLAlib.ReadsIdx`, the clamp to
$n - lo$ is harmless by `NLAlib.eighLoc_bounds`), a slot that starts no node reads $0$ and skips
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
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st st' : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one))
    (h : exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su Sg
      H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩).run st = some st') :
    H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) ∧
      H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, b ≠ Su → b ≠ Sg → ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos .uniform = st.pos .uniform + n ∧
      st'.pos .gaussian = st.pos .gaussian + 4 * (n * n) := by
  sorry

/-- **One level of the downward pass succeeds** under the standard model at $u$ with every value in
range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor conversion, if the
kernels are routines on pairs, $\ell_0 \ge 1$, $\varepsilon$ and $R_0$ decode to nonnegative values
and the arenas hold the nodes of depth $d$ (hypotheses as `NLAlib.holds_of_exec_eighDownLevel`). No
printed source.
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
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      (∃ v, st.store.read p c 2 = some v) ∧ ∃ v, st.store.read p c 3 = some v) :
    ∃ st', exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su
      Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩).run st = some st' := by
  sorry

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
    rw [exec_bindIdx_of_read I ((hSzfr p _).trans hv) hk] at h
    change exec I (.seq (.loop _ _) .skip) _ = some s₂ at h
    rw [exec_seq_skip, exec_loop] at h
    simp only [Nat.zero_min, IExp.eval_sub, IExp.eval_one, IExp.eval_var, Nat.sub_zero,
      Nat.sub_self, List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    refine ⟨hsh, hps, hfr, fun a lo' y ha hay hlt =>
      hdone a lo' y ha hay (lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) ?_)⟩
    rintro rfl
    exact hy a y ha hay
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hay).1
  rw [exec_bindIdx_of_read I ((hSzfr p _).trans hv) hk] at h
  have hb := eighLoc_bounds (by omega : 1 ≤ n) hay
  have hmin : min y.k (n - lo) = y.k := min_eq_left (by omega)
  simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var, hmin] at h
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
  obtain ⟨v, hv, k, hk⟩ : ∃ v, st.store.read p H.Sz (n * D + lo) = some v ∧
      ∃ k, I.sem.toNat p v = some k := by
    have : ∃ k, ReadsIdx I.sem st.store p H.Sz (n * D + lo) k := by
      by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = D ∧
          eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
      · obtain ⟨a, y, ha, hy⟩ := hy
        exact ⟨_, (hlev.1 a lo y ha hy).1⟩
      · push Not at hy
        exact ⟨0, hlev.2.1 lo hlo fun a y ha => hy a y ha⟩
    obtain ⟨k, hk⟩ := this
    unfold ReadsIdx at hk
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hk
    exact ⟨v, hv, k, hk⟩
  have hx : s.store.read p H.Sz (n * D + lo) = some v := (hrd p _).trans hv
  change ∃ st', exec I (.seq (.bindIdx p ⟨H.Sz, eighSlotOff (.const n) (.const D) (.var lo)⟩
    (.const n - .var lo) _) .skip) s = some st' ∧ _
  rw [exec_seq_skip, exec_bindIdx_of_read I hx hk]
  simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var]
  have hk' : min k (n - lo) ≤ n - lo := min_le_right _ _
  generalize min k (n - lo) = k' at hk' ⊢
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
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk] at h
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
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk] at h
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
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk] at h
    change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _ at h
    rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, el5_seq_loop_one rfl] at h
    obtain ⟨s₃, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    rw [exec_skip] at h
    cases h
    obtain ⟨v', hv', hk'⟩ := Option.bind_eq_some_iff.mp hkpr
    change exec I (.seq (.bindIdx _ _ _ _) .skip) _ = some _ at h₁
    rw [exec_seq_skip, exec_bindIdx_of_read I ((hRo p _ _ hKpU hKpE).trans hv') hk'] at h₁
    rw [show min kp (IExp.var y.k).eval = kp from min_eq_left hkp] at h₁
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
    rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk] at h
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
  rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk] at h
  obtain ⟨hk1, hb⟩ := eighLoc_bounds (by omega : 1 ≤ n) hay
  have hmin : min y.k (n - lo) = y.k := min_eq_left (by omega)
  simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var, hmin] at h
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
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk]
    change ∃ s₂, exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _
    rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, exec_skip]
    exact ⟨_, rfl⟩
  | shift b A' σ' =>
    rw [hs] at hr
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hr
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk]
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
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk]
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
    rw [exec_seq_skip, exec_bindIdx_of_read I ((hRo p _ _ hKpU hKpE).trans hv') hk']
    rw [show min kp (IExp.var y.k).eval = kp from min_eq_left hkp]
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
    rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk]
    change ∃ s₂, exec I (.seq (.loop _ _) .skip) _ = some s₂
    rw [el5_seq_loop_zero (by simp), exec_skip]
    exact ⟨_, rfl⟩
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hay).1
  rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk]
  obtain ⟨hk1, hb⟩ := eighLoc_bounds (by omega : 1 ≤ n) hay
  have hmin : min y.k (n - lo) = y.k := min_eq_left (by omega)
  simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var, hmin]
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
`NLAlib.eighSlotTree M n F R₀ β 0 0 root`; the final copies and the pops. L, about 160 lines. -/
theorem holds_of_exec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
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
  sorry

/-- **The refinement of the spectral bisection program, success**: under the standard model at $u$
with every value in range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor
conversion, if the kernels `mm`, `qr` of `I` are routines on interleaved pairs, $\ell_0 \ge 1$,
$\varepsilon$ and $R_0$ decode to nonnegative values, and the buffers `U`, `dv` at tag `p` have
$2n^2$ and $n$ cells (hypotheses on the inputs as `NLAlib.holds_of_exec_eighProg`), then every run
of `NLAlib.eighProg` succeeds. No printed source.
Proof: the allocations succeed; the initialisation (`lit_ok`, copies of initialised cells, the
pilot's `NLAlib.Computation.exists_exec_zcopy`); the downward loop by
`NLAlib.Computation.exists_exec_loop_eq_some_of_forall` with `NLAlib.exists_exec_eighDownLevel` and
the invariant `NLAlib.holds_of_exec_eighDownLevel` gives; `NLAlib.exists_exec_eighBottomLevel`; the
upward loop with `NLAlib.exists_exec_eighUpLevel`; the final copies and the pops. L, about 100
lines. -/
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
    (hU : ∃ len, st.store.shape[U]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hdv : ∃ len, st.store.shape[dv]? = some (p, len) ∧ n ≤ len) :
    ∃ st', exec I (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run st =
      some st' := by
  sorry

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
  exact holds_of_exec_eighProg hmm hqr p hflag N ℓ₀ F hlit htn (by simp)
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
    ⟨2 * (N * N), by simp [inputState, Store.getElem?_shape, bufs], by simp⟩
    ⟨N, by simp [inputState, Store.getElem?_shape, bufs], by simp⟩

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
  sorry

/-- **The kernel cost of the registered tree, weighted** ([Shah2024, Section 4], the operation count
of Theorem 4.2): for a cost $T$ of a kernel call by its largest dimension that is monotone and
superadditive ($T(a) + T(b) \le T(a + b)$, as a convex $T$ with $T(0) = 0$ is), under the standard
charge, every successful run of `NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$ adds
at most $(\ell_0 + 1)(2F + 12)\,T(N)$ to the weighted kernel count: per level, the nodes have sizes
summing to at most $N$, each with at most $2F + 12$ kernel calls of largest dimension at most its
size. The static bound `NLAlib.eighCount` charges every size at every slot, a factor of about $N^2$
more. No printed source.
Proof: an invariant of the run (not of `NLAlib.Computation.FStmt.staticCost`): by the shapes of
`NLAlib.holds_of_exec_eighDownLevel` and `NLAlib.holds_of_exec_eighUpLevel`, the calls of a level
are those of its nodes (`NLAlib.Computation.exec_kcall`, the kind records its dimensions, and every
dimension list of a node of size $k$ has entries at most $k$); the sizes at one depth are the
disjoint ranges of `NLAlib.eighLoc_disjoint` inside $[0, N)$, so $\sum_y T(k_y) \le T(N)$ by
superadditivity and monotonicity (`Finset.sum_le_sum`, induction on the number of nodes); sum over
the $\ell_0 + 1$ levels (`Finsupp.weight_apply`, `map_add`). L, about 150 lines. -/
theorem eighProg.weight_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (N ℓ₀ F : ℕ) (T : ℕ → ℕ)
    (hT : Monotone T) (hTsup : ∀ a b, T a + T b ≤ T (a + b)) {st st' : St P K (OpCount P ι)}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F] st = some st') :
    Finsupp.weight (fun κ : OpKind P ι => match κ with
        | .kcall _ _ ds => T (ds.foldr max 0)
        | _ => 0) st'.cnt ≤
      Finsupp.weight (fun κ : OpKind P ι => match κ with
        | .kcall _ _ ds => T (ds.foldr max 0)
        | _ => 0) st.cnt + (ℓ₀ + 1) * (2 * F + 12) * T N := by
  sorry

end NLAlib
