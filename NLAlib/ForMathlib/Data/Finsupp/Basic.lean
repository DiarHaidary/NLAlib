/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Real.Basic

/-!
# A common bound for the supports of two finitely supported sequences

Two finitely supported real sequences vanish beyond a common index, which reduces statements
about them to vectors on `Fin N`. Upstream candidate for `Mathlib.Data.Finsupp.Basic`.

## Main results

* `Finsupp.exists_forall_le_apply_eq_zero`: a common index beyond which both sequences vanish.
-/

@[expose] public section

namespace Finsupp

/-- Two finitely supported sequences vanish beyond a common index. This is how statements about
them are reduced to vectors on `Fin N`. -/
theorem exists_forall_le_apply_eq_zero (x y : ℕ →₀ ℝ) :
    ∃ N, (∀ i, N ≤ i → x i = 0) ∧ ∀ i, N ≤ i → y i = 0 := by
  classical
  obtain ⟨N, hN⟩ := (x.support ∪ y.support).exists_nat_subset_range
  refine ⟨N, fun i hi => ?_, fun i hi => ?_⟩
  · by_contra hne
    exact (Finset.mem_range.mp
      (hN (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hne)))).not_ge hi
  · by_contra hne
    exact (Finset.mem_range.mp
      (hN (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hne)))).not_ge hi

end Finsupp
