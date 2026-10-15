/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive integrands have a positive integral

An integrable function that is almost everywhere positive has a positive integral against a
nonzero measure. Mathlib has the characterisation
`MeasureTheory.integral_pos_iff_support_of_nonneg_ae` and the special case
`MeasureTheory.integral_exp_pos`. Upstream candidate for
`Mathlib.MeasureTheory.Integral.Bochner.Basic`.

## Main results

* `MeasureTheory.integral_pos_of_ae_pos`.
-/

@[expose] public section

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- An integrable function that is almost everywhere positive has a positive integral against a
nonzero measure: $\int f \, d\mu > 0$. -/
theorem integral_pos_of_ae_pos [NeZero μ] {f : α → ℝ} (hf : Integrable f μ)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) : 0 < ∫ x, f x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ h => h.le) hf,
    measure_congr (Filter.eventuallyEq_univ.2 (hpos.mono fun _ h => h.ne') :
      Function.support f =ᵐ[μ] Set.univ)]
  exact Measure.measure_univ_pos.2 (NeZero.ne μ)

end MeasureTheory
