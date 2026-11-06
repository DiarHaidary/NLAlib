/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.InterpMachine
public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.RandomMatrix.Tape

/-!
# The complex Gaussian matrix of a Gaussian tape (scaffold)

Statement for a new file `NLAlib/RandomMatrix/Computation/ComplexTape.lean` (stage COMPDYN S1d,
design note `docs/design/Computation-SignDeflatePrograms.md`, §4): the ideal sample a program
draws from the Gaussian tape, two real draws per complex entry scaled by $1/\sqrt2$
(`NLAlib.Computation.tapeComplexMatrix`), is a standard complex Gaussian matrix.

## Main results

* `NLAlib.Computation.hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Computation

/-- **A Gaussian tape draws a complex Gaussian matrix**: if $\xi$ has the law of the tape
`NLAlib.Computation.tapeLaw` under $\mu$, the $n \times n$ matrix with entry $(i, j)$ equal to
$(\xi_{2(i + nj)} + i\,\xi_{2(i + nj) + 1})/\sqrt2$, from the Gaussian draws, has the law of a
matrix with independent standard complex Gaussian entries (`NLAlib.complexGaussianMatrix`). No
printed source.
Proof: `NLAlib.Computation.hasLaw_apply_of_hasLaw_tapeLaw` gives the Gaussian tape as an i.i.d.
sequence of standard Gaussians; the positions $(i, j, t) \mapsto 2(i + nj) + t$ are injective
(the injectivity argument of `NLAlib.hasLaw_tapeMatrix_of_hasLaw_iidSequence`), so
`ProbabilityTheory.HasLaw.comp_of_injective` (`NLAlib/Probability/Law.lean`) gives an i.i.d.
family indexed by `Fin n × Fin n × Fin 2`; scaling by
$1/\sqrt2$ maps `gaussianReal 0 1` to `gaussianReal 0 2⁻¹` (`gaussianReal_map_const_mul`); a
product of copies of that pair law mapped by `Complex.measurableEquivRealProd.symm` is
`NLAlib.complexGaussian`, and regrouping the product by rows
(`MeasureTheory.measurePreserving_piCongrLeft`, `Measure.pi_pi`) gives
`NLAlib.complexGaussianMatrix`. M, about 60 lines. -/
theorem hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw {Ω : Type} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ) (n : ℕ) :
    HasLaw (fun ω => tapeComplexMatrix (ξ ω .gaussian) n)
      (complexGaussianMatrix (Fin n) (Fin n)) μ := by
  sorry

end NLAlib.Computation
