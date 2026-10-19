/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Finsupp.Order

/-!
# The absolute value of a finitely supported function

The lattice absolute value $\lvert f \rvert = f \sqcup -f$ of a finitely supported function is
taken pointwise. Upstream candidate for `Mathlib.Data.Finsupp.Order`.

## Main results

* `Finsupp.abs_apply`: $\lvert f \rvert(i) = \lvert f(i) \rvert$.
-/

@[expose] public section

namespace Finsupp

/-- The absolute value of a finitely supported function is taken pointwise:
$\lvert f \rvert(i) = \lvert f(i) \rvert$. -/
@[simp]
theorem abs_apply {ι M : Type*} [Lattice M] [AddGroup M] (f : ι →₀ M) (i : ι) :
    |f| i = |f i| := by
  rw [abs, sup_apply, neg_apply]
  rfl

end Finsupp
