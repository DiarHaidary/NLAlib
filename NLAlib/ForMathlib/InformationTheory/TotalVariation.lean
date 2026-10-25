/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real

/-!
# Total variation distance between measures

The total variation distance $\sup_A \lvert\mu(A) - \nu(A)\rvert$ over measurable sets, real
valued. Mathlib (v4.33.1) has the total variation of a signed measure
(`MeasureTheory.SignedMeasure.totalVariation`) and the Kullback–Leibler divergence
`InformationTheory.klDiv`, but no distance between two probability measures; the theorems
(data processing, Le Cam's two-point bound, Pinsker's inequality) are in the scaffold. Upstream
candidate, next to `Mathlib/InformationTheory/KullbackLeibler`.

## Main definitions

* `InformationTheory.tvDist`.
-/

@[expose] public section

open MeasureTheory

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- The **total variation distance** between two measures,
$\sup_{A} \lvert\mu(A) - \nu(A)\rvert$ over measurable sets $A$, with `Measure.real` values. For
probability measures it lies in $[0, 1]$; for measures with infinite mass the real values are
junk (`Measure.real` of an infinite measure is $0$). -/
noncomputable def tvDist (μ ν : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |μ.real A - ν.real A|

end InformationTheory
