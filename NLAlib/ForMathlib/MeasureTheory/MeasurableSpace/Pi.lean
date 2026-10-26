/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Measurability of appending to a tuple

Appending an entry to a tuple, `Fin.snoc`, is measurable in the tuple and the entry: the
measurable analogue of Mathlib's `Continuous.finSnoc`, for tuples with one value type. It is the
step that extends a history of queries by one response. Upstream candidate for
`Mathlib/MeasureTheory/MeasurableSpace/Pi.lean`.

## Main results

* `Measurable.finSnoc`: `Fin.snoc` of measurable functions is measurable.
-/

@[expose] public section

/-- `Fin.snoc` of measurable functions is measurable. The measurable analogue of
`Continuous.finSnoc`, for tuples with one value type. -/
@[fun_prop]
theorem Measurable.finSnoc {α R : Type*} [MeasurableSpace α] [MeasurableSpace R] {i : ℕ}
    {f : α → Fin i → R} {g : α → R} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => (Fin.snoc (f a) (g a) : Fin (i + 1) → R) := by
  refine measurable_pi_lambda _ fun j => ?_
  induction j using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using hg
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp hf
