/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# Complex Gaussian vectors and matrices

`NLAlib.complexGaussian` is the standard complex Gaussian law $\mathcal{N}_{\mathbb{C}}(0, 1)$ on
$\mathbb{C}$: the real and imaginary parts are independent centred Gaussians of variance $1/2$,
so that $\mathbb{E}\lvert z \rvert^2 = 1$. `NLAlib.complexGaussianVector n` and
`NLAlib.complexGaussianMatrix m n` are the laws of a vector and of a matrix with independent
standard complex Gaussian entries, written as products as the real laws
`NLAlib.gaussianVector` and `NLAlib.gaussianMatrix` are. Mathlib's `stdGaussian ℂ` is the real
two-dimensional standard Gaussian on $\mathbb{C}$, of variance $1$ in each part, which is
$\sqrt2$ times a standard complex Gaussian. These are the test matrices of randomized deflation
([Shah2024, Section 3]), whose analysis uses the norm tail of
[BanksKulkarniMukherjeeSrivastava2021] and, in place of the exact law of the smallest singular
value [Edelman1988], an elementary small-ball bound.

## Main definitions

* `NLAlib.complexGaussian`, `NLAlib.complexGaussianVector`, `NLAlib.complexGaussianMatrix`.

## Main results

* `NLAlib.isProbabilityMeasure_complexGaussian`,
  `NLAlib.isProbabilityMeasure_complexGaussianVector`,
  `NLAlib.isProbabilityMeasure_complexGaussianMatrix`.

The invariance, norm and smallest-singular-value tails are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` (stage HDIAG).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Matrix

namespace NLAlib

/-- The **standard complex Gaussian law** $\mathcal{N}_{\mathbb{C}}(0, 1)$: the law of
$x + iy$ for independent real $x, y \sim \mathcal{N}(0, 1/2)$. -/
noncomputable def complexGaussian : Measure ℂ :=
  ((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)).map Complex.measurableEquivRealProd.symm

/-- The standard complex Gaussian law is a probability measure. -/
instance isProbabilityMeasure_complexGaussian : IsProbabilityMeasure complexGaussian :=
  Measure.isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

/-- The law of a vector with independent standard complex Gaussian entries. -/
noncomputable abbrev complexGaussianVector (n : Type*) [Fintype n] : Measure (n → ℂ) :=
  Measure.pi fun _ : n => complexGaussian

/-- The complex Gaussian vector law is a probability measure. -/
instance isProbabilityMeasure_complexGaussianVector (n : Type*) [Fintype n] :
    IsProbabilityMeasure (complexGaussianVector n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : n => complexGaussian))

/-- The law of a matrix with independent standard complex Gaussian entries, written as
independent rows, each a standard complex Gaussian vector. -/
noncomputable abbrev complexGaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    Measure (Matrix m n ℂ) :=
  Measure.pi fun _ : m => complexGaussianVector n

/-- The complex Gaussian matrix law is a probability measure. -/
instance isProbabilityMeasure_complexGaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    IsProbabilityMeasure (complexGaussianMatrix m n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : m => complexGaussianVector n))

end NLAlib
