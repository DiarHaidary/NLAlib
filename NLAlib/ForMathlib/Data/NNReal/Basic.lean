/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform weights in $\mathbb{R}_{\ge 0}$

The uniform weights $1/\lvert \iota \rvert$ on a nonempty finite type sum to one. Upstream
candidate for `Mathlib.Data.NNReal.Basic`.

## Main results

* `NNReal.sum_const_inv_card`: $\sum_{i \in \iota} 1/\lvert \iota \rvert = 1$.
-/

@[expose] public section

open scoped NNReal

namespace NNReal

/-- The uniform weights $1/\lvert \iota \rvert$ sum to one on a nonempty finite type: the
normalisation hypothesis $\sum_i p_i = 1$ of a sampling law at uniform weights. -/
theorem sum_const_inv_card {ι : Type*} [Fintype ι] [Nonempty ι] :
    ∑ _ : ι, (Fintype.card ι : ℝ≥0)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

end NNReal
