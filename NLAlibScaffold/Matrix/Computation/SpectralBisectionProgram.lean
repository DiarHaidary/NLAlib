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
  sorry

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
  sorry

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
