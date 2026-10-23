/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.Law

/-!
# Rademacher matrices

`NLAlib.rademacherMatrix m n` is the law of an $m \times n$ real matrix with independent random
signs, written as independent rows, each a `rademacherVector n`:
`Measure.pi fun _ : m => rademacherVector n`. It mirrors `NLAlib.gaussianMatrix`: an `abbrev`,
so the product-law lemmas apply directly (`ProbabilityTheory.HasLaw.eval` for the rows,
`ProbabilityTheory.HasLaw.iIndepFun_eval` for their independence), and the facts a consumer
needs are stated here. A Rademacher matrix read as a vector indexed by $m \times n$
(`Function.uncurry`) is a `rademacherVector`; its columns are independent sign vectors; its
transpose is again a Rademacher matrix.

Design: Sketching stage S3 (`docs/design/Sketching-S3.md` §3.3), moved here by the consolidation
round (`docs/design/Consolidation.md` §3.6, R1).

## Main definitions

* `NLAlib.rademacherMatrix m n`.

## Main results

* `NLAlib.hasLaw_uncurry_of_hasLaw_rademacherMatrix`,
  `NLAlib.hasLaw_rademacherMatrix_of_hasLaw_uncurry`.
* `NLAlib.hasLaw_col_of_hasLaw_rademacherMatrix`,
  `NLAlib.iIndepFun_col_of_hasLaw_rademacherMatrix`.
* `NLAlib.hasLaw_conjTranspose_of_hasLaw_rademacherMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The law of a matrix with independent random signs: independent rows, each a
`rademacherVector n`. -/
noncomputable abbrev rademacherMatrix (k n : Type*) [Fintype k] [Fintype n] :
    Measure (Matrix k n ℝ) :=
  Measure.pi fun _ : k => rademacherVector n

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- The Rademacher matrix law is a probability measure. -/
instance isProbabilityMeasure_rademacherMatrix : IsProbabilityMeasure (rademacherMatrix m n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : m => rademacherVector n))

/-- A Rademacher matrix read as a vector indexed by $m \times n$ is a vector of independent
random signs. -/
theorem hasLaw_uncurry_of_hasLaw_rademacherMatrix (hX : HasLaw X (rademacherMatrix m n) μ) :
    HasLaw (fun ω => Function.uncurry (X ω)) (rademacherVector (m × n)) μ :=
  (measurePreserving_curry_pi (ν := fun _ _ => rademacherMeasure)).symm.fun_comp_hasLaw hX

/-- A random matrix whose entries, as a vector indexed by $m \times n$, are independent random
signs is a Rademacher matrix. -/
theorem hasLaw_rademacherMatrix_of_hasLaw_uncurry
    (hX : HasLaw (fun ω => Function.uncurry (X ω)) (rademacherVector (m × n)) μ) :
    HasLaw X (rademacherMatrix m n) μ :=
  (measurePreserving_curry_pi (ν := fun _ _ => rademacherMeasure)).fun_comp_hasLaw hX

/-- The transpose of a Rademacher matrix, as a family of rows: transposition permutes the
coordinates of the flattened sign vector. -/
private theorem hasLaw_pi_col (hX : HasLaw X (rademacherMatrix m n) μ) :
    HasLaw (fun ω j i => X ω i j) (Measure.pi fun _ : n => rademacherVector m) μ := by
  refine hasLaw_rademacherMatrix_of_hasLaw_uncurry (X := fun ω => (X ω)ᵀ) ?_
  exact (measurePreserving_arrowCongr' (fun _ : m × n => rademacherMeasure)
    (fun _ : n × m => rademacherMeasure) (Equiv.prodComm m n) (MeasurableEquiv.refl ℝ)
    fun _ => MeasurePreserving.id _).fun_comp_hasLaw
      (hasLaw_uncurry_of_hasLaw_rademacherMatrix hX)

/-- The columns of a Rademacher matrix are vectors of independent random signs. -/
theorem hasLaw_col_of_hasLaw_rademacherMatrix (hX : HasLaw X (rademacherMatrix m n) μ)
    (j : n) :
    HasLaw (fun ω i => X ω i j) (rademacherVector m) μ :=
  (hasLaw_pi_col hX).eval j

/-- The columns of a Rademacher matrix are independent. -/
theorem iIndepFun_col_of_hasLaw_rademacherMatrix (hX : HasLaw X (rademacherMatrix m n) μ) :
    iIndepFun (fun j ω i => X ω i j) μ :=
  (hasLaw_pi_col hX).iIndepFun_eval

/-- The conjugate transpose of a Rademacher matrix is a Rademacher matrix: its rows are the
independent sign columns. -/
theorem hasLaw_conjTranspose_of_hasLaw_rademacherMatrix
    (hX : HasLaw X (rademacherMatrix m n) μ) :
    HasLaw (fun ω => (X ω)ᴴ) (rademacherMatrix n m) μ := by
  have hfun : (fun ω => (X ω)ᴴ) = fun ω => Matrix.of fun j i => X ω i j := by
    funext ω
    ext j i
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
  rw [hfun]
  exact hasLaw_pi_col hX

end NLAlib
