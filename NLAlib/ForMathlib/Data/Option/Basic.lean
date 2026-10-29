/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Option.Basic

/-!
# Mapping a successful option

If an option succeeds with a value satisfying `Q`, and `f` sends values satisfying `Q` to values
satisfying `R`, then its map by `f` succeeds with a value satisfying `R`: the last step of a run
lemma whose run is a loop followed by a pop of the scratch buffer. Upstream candidate for
`Mathlib.Data.Option.Basic`.

## Main results

* `Option.exists_map_eq_some_of_exists`.
-/

@[expose] public section

namespace Option

/-- If `o` is `some a` for an `a` satisfying `Q`, and `f` maps every value satisfying `Q` to one
satisfying `R`, then `o.map f` is `some b` for a `b` satisfying `R`. -/
theorem exists_map_eq_some_of_exists {α β : Type*} {o : Option α} {f : α → β} {Q : α → Prop}
    {R : β → Prop} (h : ∃ a, o = some a ∧ Q a) (hQ : ∀ a, Q a → R (f a)) :
    ∃ b, o.map f = some b ∧ R b := by
  obtain ⟨a, rfl, ha⟩ := h
  exact ⟨f a, rfl, hQ a ha⟩

end Option
