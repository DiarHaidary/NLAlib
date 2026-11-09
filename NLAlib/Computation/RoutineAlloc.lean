/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineSpec

/-!
# Chains of allocations in routine specifications

A block that allocates several scratch buffers of different lengths in a row is specified from the
state after all its allocations, by named states: `NLAlib.Computation.St.allocs` is the state after
allocating buffers of given lengths, `NLAlib.Computation.St.releases` the state after releasing
them, and `NLAlib.Computation.spec_allocBind_chain` peels one allocation off the chain, as
`NLAlib.Computation.spec_allocBind_iterate` does for buffers of one length.

## Main results

* `NLAlib.Computation.St.allocs_facts`, `NLAlib.Computation.St.releases_facts`: the old buffers,
  their shapes and the tape positions are as they were.
* `NLAlib.Computation.spec_allocBind_chain`: the $j$-th allocation of a chain.
-/

@[expose] public section

namespace NLAlib.Computation
variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] {I : Interp P ι K C}

/-- The state after allocating buffers of the lengths `ls`, in order, at tag `p` and width `w`. -/
def St.allocs (st : St P K C) (p : P) (w : ℕ) (ls : List ℕ) : St P K C :=
  ls.foldl (fun s l => s.allocate p l w) st

/-- The state after releasing buffers of the lengths `ls`, the last first. -/
def St.releases (st : St P K C) (p : P) (w : ℕ) (ls : List ℕ) : St P K C :=
  ls.foldr (fun l s => s.release p l w) st

omit [AddMonoid C] in
/-- One more allocation at the end of a chain. -/
theorem St.allocs_append_singleton (st : St P K C) (p : P) (w : ℕ) (ls : List ℕ) (l : ℕ) :
    st.allocs p w (ls ++ [l]) = (st.allocs p w ls).allocate p l w := by
  simp [St.allocs, List.foldl_append]

omit [AddMonoid C] in
/-- One more release at the start of a chain of releases. -/
theorem St.releases_append_singleton (st : St P K C) (p : P) (w : ℕ) (ls : List ℕ) (l : ℕ) :
    st.releases p w (ls ++ [l]) = (st.release p l w).releases p w ls := by
  simp [St.releases, List.foldr_append]

omit [AddMonoid C] in
/-- Allocations of the lengths `ls` push `ls.length` buffers of those lengths and leave the old
buffers, their shapes and the tape positions as they were. -/
theorem St.allocs_facts (st : St P K C) (p : P) (w : ℕ) (ls : List ℕ) :
    (st.allocs p w ls).store.size = st.store.size + ls.length ∧
    (∀ x < st.store.size, (st.allocs p w ls).store.shape[x]? = st.store.shape[x]? ∧
      ∀ q i, (st.allocs p w ls).store.read q x i = st.store.read q x i) ∧
    (∀ j < ls.length,
      (st.allocs p w ls).store.shape[st.store.size + j]? = some (p, ls.getD j 0)) ∧
    (st.allocs p w ls).pos = st.pos := by
  induction ls using List.reverseRecOn with
  | nil =>
    exact ⟨rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩
  | append_singleton ls l ih =>
    obtain ⟨hs, hr, hn, hp⟩ := ih
    rw [St.allocs_append_singleton]
    refine ⟨by rw [St.size_allocate, hs, List.length_append, List.length_singleton]; ring,
      fun x hx => ⟨?_, fun q i => ?_⟩, fun j hj => ?_, hp⟩
    · rw [St.shape_allocate, Array.getElem?_push, if_neg (by rw [Store.size_shape, hs]; omega),
        (hr x hx).1]
    · rw [St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega), (hr x hx).2]
    · rw [St.shape_allocate, Array.getElem?_push]
      split_ifs with h
      · rw [Store.size_shape, hs] at h
        simp only [List.length_append, List.length_singleton] at hj
        have : j = ls.length := by omega
        subst this
        simp
      · rw [Store.size_shape, hs] at h
        simp only [List.length_append, List.length_singleton] at hj
        rw [hn j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]

omit [AddMonoid C] in
/-- Releasing `ls.length` buffers from a store of `b + ls.length` buffers leaves the first `b`
as they were. -/
theorem St.releases_facts (p : P) (w : ℕ) (ls : List ℕ) : ∀ (s : St P K C) (b : ℕ),
    s.store.size = b + ls.length →
    (s.releases p w ls).store.size = b ∧
    (∀ x < b, (s.releases p w ls).store.shape[x]? = s.store.shape[x]? ∧
      ∀ q i, (s.releases p w ls).store.read q x i = s.store.read q x i) ∧
    (s.releases p w ls).pos = s.pos := by
  induction ls using List.reverseRecOn with
  | nil => intro s b h; exact ⟨h, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, rfl⟩
  | append_singleton ls l ih =>
    intro s b h
    rw [St.releases_append_singleton]
    simp only [List.length_append, List.length_singleton] at h
    obtain ⟨hs, hr, hp⟩ := ih (s.release p l w) b (by simp [St.release]; omega)
    refine ⟨hs, fun x hx => ⟨?_, fun q i => ?_⟩, hp⟩
    · rw [(hr x hx).1]
      simp only [St.release]
      rw [Store.shape_pop, Array.getElem?_pop, if_pos (by rw [Store.size_shape]; omega)]
    · rw [(hr x hx).2]
      simp only [St.release]
      exact Store.read_pop_of_lt (by omega)


variable {m : Mode} {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
  {fp : List (ℕ × ℕ × ℕ)}

/-- **The $j$-th of a chain of allocations of different lengths**, by named states: as
`NLAlib.Computation.spec_allocBind_iterate` with the lengths `ls`. -/
theorem spec_allocBind_chain {p : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {b : ℕ}
    (ls : List ℕ) (j : ℕ) (hj : ls[j]? = some len.eval)
    (hb : ∀ st, pre st → st.store.size = b)
    (h : Spec m I (fun s => ∃ st, pre st ∧ s = st.allocs p (I.width p) (ls.take (j + 1)))
      (f (b + j)).run (fp ++ (List.range (j + 1)).map fun i => (b + i, 0, ls.getD i 0))
      fun s s' => ∀ st, pre st → s = st.allocs p (I.width p) (ls.take (j + 1)) →
        post st (s'.releases p (I.width p) (ls.take (j + 1)))) :
    Spec m I (fun s => ∃ st, pre st ∧ s = st.allocs p (I.width p) (ls.take j))
      (Builder.alloc p len >>= f).run (fp ++ (List.range j).map fun i => (b + i, 0, ls.getD i 0))
      fun s s' => ∀ st, pre st → s = st.allocs p (I.width p) (ls.take j) →
        post st (s'.releases p (I.width p) (ls.take j)) := by
  have hlt : j < ls.length := (List.getElem?_eq_some_iff.mp hj).1
  have hge : ls[j] = len.eval := (List.getElem?_eq_some_iff.mp hj).2
  have htake : ls.take (j + 1) = ls.take j ++ [len.eval] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, ← hge]; rfl
  have hsz : ∀ st, pre st → (st.allocs p (I.width p) (ls.take j)).store.size = b + j := by
    intro st hst
    rw [(St.allocs_facts st p (I.width p) (ls.take j)).1, hb st hst, List.length_take]
    omega
  have hgd : ls.getD j 0 = len.eval := by rw [List.getD_eq_getElem?_getD, hj]; rfl
  rw [List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc, htake, hgd] at h
  refine Spec.allocBind h (fun _ ⟨st, hst, e⟩ => e ▸ hsz st hst)
    (fun _ _ ⟨st, hst, e⟩ e₁ => ⟨st, hst, by rw [e₁, e, St.allocs_append_singleton]⟩)
    fun _ _ s₂ ⟨st₀, hst₀, e⟩ e₁ hp st hst e' => ?_
  rw [← St.releases_append_singleton]
  exact hp st hst (by rw [St.allocs_append_singleton, ← e', ← e₁])

end NLAlib.Computation
