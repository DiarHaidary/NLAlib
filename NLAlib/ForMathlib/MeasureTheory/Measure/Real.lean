/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real

/-!
# Almost-everywhere monotonicity of the real-valued measure

$\mu(s) \le \mu(t)$ for the real-valued measure `μ.real` when $s \subseteq t$ outside a null set
and $\mu(t)$ is finite. No measurability is needed. Mathlib has `MeasureTheory.measureReal_mono`
(an inclusion) and `MeasureTheory.measureReal_mono_null`; this is the almost-everywhere form,
the step that bounds a tail by the tail of a larger event that contains it almost surely.
Upstream candidate for `Mathlib/MeasureTheory/Measure/Real.lean`.


## Main results

* `MeasureTheory.measureReal_mono_ae`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- Monotonicity of `μ.real` along an almost-everywhere inclusion: $\mu(s) \le \mu(t)$ when
$s \subseteq t$ almost everywhere and $\mu(t) < \infty$. Upstream candidate. -/
theorem measureReal_mono_ae {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s t : Set α}
    (h : s ≤ᵐ[μ] t) (ht : μ t ≠ ∞ := by finiteness) : μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono ht (measure_mono_ae h)

end MeasureTheory
