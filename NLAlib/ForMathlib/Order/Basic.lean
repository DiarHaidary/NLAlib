/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Order.Lattice

/-!
# Raising a coordinate to a common maximum

If `f` lies below `g` with the coordinate `p` of `g` raised to `max (g p) c`, then raising the
coordinate `p` of `f` by the same `c` stays below. Upstream candidate for `Mathlib.Order.Basic`,
next to `Function.update_le_update_iff`.

## Main results

* `Function.update_max_le_update_max`.
-/

@[expose] public section

namespace Function

/-- If `f ≤ update g p (max (g p) c)`, then
`update f p (max (f p) c) ≤ update g p (max (g p) c)`. -/
theorem update_max_le_update_max {P α : Type*} [DecidableEq P] [LinearOrder α]
    {f g : P → α} {p : P} {c : α}
    (h : f ≤ update g p (max (g p) c)) :
    update f p (max (f p) c) ≤ update g p (max (g p) c) :=
  update_le_update_iff.2 ⟨max_le (by simpa using h p) (le_max_right _ _),
    fun j hj => by simpa [update_of_ne hj] using h j⟩

end Function
