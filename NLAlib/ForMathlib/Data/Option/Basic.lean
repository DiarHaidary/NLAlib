/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Option.Basic

/-!
# Mapping and binding a successful option

If an option succeeds with a value satisfying `Q`, and `f` sends values satisfying `Q` to values
satisfying `R`, then its map by `f` succeeds with a value satisfying `R`: the last step of a run
lemma whose run is a loop followed by a pop of the scratch buffer. Likewise its bind by `f`
succeeds when `f` succeeds on every value satisfying `Q`: one step of a proof that a sequence of
runs succeeds. Upstream candidate for `Mathlib.Data.Option.Basic`.

## Main results

* `Option.exists_map_eq_some_of_exists`, `Option.exists_map_eq_some`.
* `Option.exists_bind_eq_some_of_exists`.
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

/-- If `o` is `some a`, then `o.map f` is `some b`. -/
theorem exists_map_eq_some {α β : Type*} {o : Option α} {f : α → β} (h : ∃ a, o = some a) :
    ∃ b, o.map f = some b := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f a, rfl⟩

/-- If `o` is `some a` for an `a` satisfying `Q`, and `f` succeeds on every value satisfying `Q`,
then `o.bind f` succeeds. -/
theorem exists_bind_eq_some_of_exists {α β : Type*} {o : Option α} {f : α → Option β}
    (Q : α → Prop) (h : ∃ a, o = some a ∧ Q a) (hQ : ∀ a, Q a → ∃ b, f a = some b) :
    ∃ b, o.bind f = some b := by
  obtain ⟨a, rfl, ha⟩ := h
  exact hQ a ha

end Option
