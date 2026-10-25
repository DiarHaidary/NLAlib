/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of continuous functions carried by an interval

A function continuous on a compact interval $[a, b]$ is integrable against a finite measure on
$\mathbb{R}$ that is carried by $[a, b]$: the integral over $[a, b]$ is the integral over the whole
line, because the measure restricted to $[a, b]$ is the measure itself. Upstream candidate for
`Mathlib.MeasureTheory.Integral.IntegrableOn`, beside `ContinuousOn.integrableOn_Icc`.

## Main results

* `ContinuousOn.integrable_of_ae_mem_Icc`: a function continuous on $[a, b]$ is integrable against a
  finite measure carried by $[a, b]$.
-/

@[expose] public section

namespace MeasureTheory

/-- A function continuous on $[a, b]$ is integrable against a finite measure $\mu$ on $\mathbb{R}$
carried by $[a, b]$. -/
theorem _root_.ContinuousOn.integrable_of_ae_mem_Icc {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} {f : ℝ → E}
    (hf : ContinuousOn f (Set.Icc a b)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : Integrable f μ := by
  have h := hf.integrableOn_Icc (μ := μ)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h

end MeasureTheory
