/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Rank

/-!
# A Gaussian matrix avoids affine sets: the theorems of stage LB-A

Statements for `NLAlib/RandomMatrix/Gaussian/Rank.lean` whose proofs are deferred
(`docs/design/Probability-MatvecQueryModel.md`, §3.5): a nonzero two-sided linear image of a
standard Gaussian matrix takes any given value with probability zero. This is the measure-zero
step of the exact range-recovery lower bound.

## Main results

* `NLAlib.measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- **A Gaussian matrix hits a point of a nonzero linear image with probability zero**: for a
standard Gaussian $\mathbf{X} \in \mathbb{R}^{m \times n}$, matrices
$\mathbf{N} \ne \mathbf{0}$ and $\mathbf{F} \ne \mathbf{0}$ and any $\mathbf{C}$,
$\mathbb{P}[\mathbf{N}\mathbf{X}\mathbf{F} = \mathbf{C}] = 0$.
Proof: M, about 25 lines. Pick $i, a$ with $\mathbf{N}_{i,a} \ne 0$ and $b, j$ with
$\mathbf{F}_{b,j} \ne 0$ (`Matrix.ext` contrapositive). The event lies in
$\{(\mathbf{N}\mathbf{X}\mathbf{F})_{i,j} = \mathbf{C}_{i,j}\}$, and
$(\mathbf{N}\mathbf{X}\mathbf{F})_{i,j} = \langle \mathrm{vec}\,\mathbf{X}, \mathbf{c}\rangle$
with $\mathbf{c}_{(a, b)} = \mathbf{N}_{i,a}\mathbf{F}_{b,j}$ (`Matrix.mul_apply`,
`Finset.sum_product`), a nonzero vector. By `hasLaw_uncurry_of_hasLaw_gaussianMatrix` and
`hasLaw_dotProduct_of_hasLaw_gaussianVector` it is a centred Gaussian with variance
$\lVert\mathbf{c}\rVert^2 > 0$, which has no atoms (`noAtoms_gaussianReal`,
`Measure.map_apply` at the singleton); `measure_mono_null`. -/
theorem measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix {p r : Type*}
    (hX : HasLaw X (gaussianMatrix m n) μ) {N : Matrix p m ℝ} {F : Matrix n r ℝ} (hN : N ≠ 0)
    (hF : F ≠ 0) (C : Matrix p r ℝ) :
    μ {ω | N * X ω * F = C} = 0 := by
  sorry

end NLAlib
