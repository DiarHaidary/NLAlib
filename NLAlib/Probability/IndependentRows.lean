/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Law

/-!
# Independent entries give independent rows

A random matrix whose entries, indexed by `m × n`, are independent has independent rows. Mathlib
has the converse direction for families of independent vectors with independent coordinates
(`ProbabilityTheory.iIndepFun_uncurry'`). This is the bridge from the entry hypotheses of
`ProbabilityTheory.HasLaw.iIndepFun_entry`'s shape to the row hypotheses of the sub-Gaussian
rows theorems (`NLAlib/Sketching/Gaussian/SubGaussian.lean`).

This file is a skeleton of Sketching stage S3 (`docs/design/Sketching-S3.md` §3.2). At the
wrap-up it merges into `NLAlib/Probability/Law.lean`.

## Main results

* `NLAlib.iIndepFun_row_of_iIndepFun_entry`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n α : Type*} [Finite m]
  [Finite n] [MeasurableSpace α]

/-- Independent entries give independent rows: if the entries of `X : Ω → Matrix m n α`, as a
family indexed by `m × n`, are independent, so are its rows. The measurability hypothesis is the
one the product-law route needs (`NLAlib.hasLaw_pi_pi_iff` with `ν i j := μ.map (X · i j)`, then
`ProbabilityTheory.HasLaw.iIndepFun_eval`); it goes if a Mathlib grouping lemma (`iIndepFun` over
a partition of the index) turns up. Mathlib has the converse,
`ProbabilityTheory.iIndepFun_uncurry'`. -/
theorem iIndepFun_row_of_iIndepFun_entry {X : Ω → Matrix m n α}
    (hind : iIndepFun (fun p : m × n => fun ω => X ω p.1 p.2) μ)
    (hX : ∀ i j, AEMeasurable (fun ω => X ω i j) μ) : iIndepFun (fun i ω => X ω i) μ := by
  sorry

end NLAlib
