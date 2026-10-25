/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Real.Basic

/-!
# Sorting a real vector in non-increasing order

Every real vector on a finite index type $\iota$ becomes non-increasing after relabelling its
indices by `Fin` $\lvert \iota \rvert$, through Mathlib's `Tuple.sort`. This reduces statements
about the largest entries of a vector, or about majorization, to sorted vectors. Upstream
candidate for `Mathlib.Data.Fin.Tuple.Sort`.

## Main results

* `Fintype.exists_equiv_antitone_comp`: a relabelling that sorts a vector.
-/

@[expose] public section

namespace Fintype

/-- Sorting: every real vector on a finite index type $\iota$ is non-increasing after
relabelling its indices by `Fin` $\lvert \iota \rvert$. -/
theorem exists_equiv_antitone_comp {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, Antitone (a ∘ e) := by
  classical
  refine ⟨(Tuple.sort fun j => -a ((Fintype.equivFin ι).symm j)).trans (Fintype.equivFin ι).symm,
    fun i j hij => ?_⟩
  have h := Tuple.monotone_sort (fun j => -a ((Fintype.equivFin ι).symm j)) hij
  simpa only [Function.comp_apply, neg_le_neg_iff, Equiv.trans_apply] using h

end Fintype
