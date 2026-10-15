/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Finset.Max

/-!
# A common strict bound for a finite family

A finite family of values below $s$ has a single bound $M < s$ above a prescribed $a < s$: the
step of a net argument that turns "every point of the net is good, with margin" into a uniform
margin. Upstream candidate for `Mathlib.Data.Finset.Max`.

## Main results

* `Finset.exists_le_lt_of_forall_lt`.
-/

@[expose] public section

namespace Finset

/-- A finite family strictly below $s$ has a common bound $M$ with $a \le M < s$, for any
$a < s$: take $M = \max(\{a\} \cup f(S))$. -/
theorem exists_le_lt_of_forall_lt {ι α : Type*} [LinearOrder α] (S : Finset ι) (f : ι → α)
    {a s : α} (hs : a < s) (h : ∀ i ∈ S, f i < s) : ∃ M, a ≤ M ∧ M < s ∧ ∀ i ∈ S, f i ≤ M := by
  classical
  refine ⟨(insert a (S.image f)).max' (insert_nonempty _ _),
    le_max' _ _ (mem_insert_self _ _), ?_, fun i hi => le_max' _ _
      (mem_insert_of_mem (mem_image_of_mem f hi))⟩
  rw [max'_lt_iff]
  intro y hy
  rcases mem_insert.mp hy with rfl | hy
  · exact hs
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    exact h i hi

end Finset
