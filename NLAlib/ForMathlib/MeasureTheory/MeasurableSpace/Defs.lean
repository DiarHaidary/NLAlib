/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# A discrete measurable space is the top σ-algebra

A measurable space in which every set is measurable (`DiscreteMeasurableSpace`) is `⊤`. On a
finite or countable type, Mathlib's instance `MeasurableSingletonClass.toDiscreteMeasurableSpace`
makes every measurable space with measurable singletons discrete, so a law defined with `⊤` on a
finite index type can be restated under the user's own instances by `obtain rfl`. The analogue of
Mathlib's `DiscreteTopology.eq_bot`. Upstream candidate for
`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`.

## Main results

* `DiscreteMeasurableSpace.eq_top`: a discrete measurable space is `⊤`.
-/

@[expose] public section

/-- A discrete measurable space is `⊤`: every set is measurable. The analogue of Mathlib's
`DiscreteTopology.eq_bot`; on a countable type with measurable singletons it applies through
`MeasurableSingletonClass.toDiscreteMeasurableSpace`. -/
theorem DiscreteMeasurableSpace.eq_top {α : Type*} [m : MeasurableSpace α]
    [DiscreteMeasurableSpace α] : m = ⊤ :=
  eq_top_iff.2 fun _ _ => MeasurableSet.of_discrete
