/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exact
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# Test matrices drawn from a random tape

A program draws its random numbers from a tape, one i.i.d. sequence per distribution
(`docs/design/Computation.md`, D12), and stores an $N \times k$ test matrix column-major:
`NLAlib.Computation.tapeMatrix x off N k` has entry $(i, j)$ equal to tape value
$\mathit{off} + i + Nj$. With a standard Gaussian tape the matrix drawn is a standard Gaussian
matrix, and two matrices drawn from disjoint stretches of the tape are independent. These are the
laws the probabilistic theorems about programs need, so that a program that draws its own test
matrices inherits the tail bounds of its specification with no new probability.

## Main results

* `NLAlib.hasLaw_tapeMatrix_of_hasLaw_iidSequence`: a Gaussian tape draws a Gaussian matrix.
* `NLAlib.indepFun_tapeMatrix_of_hasLaw_iidSequence`: consecutive draws are independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

open Computation

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **A Gaussian tape draws a Gaussian matrix**: if the tape $x$ is an i.i.d. sequence of standard
Gaussians, the $N \times k$ matrix drawn from it from position $\mathit{off}$, column-major, is a
standard Gaussian matrix. No printed source.
Result: tape-gaussian-matrix -/
theorem hasLaw_tapeMatrix_of_hasLaw_iidSequence {x : Ω → ℕ → ℝ}
    (hx : HasLaw x (iidSequence (gaussianReal 0 1)) μ) (off N k : ℕ) :
    HasLaw (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) off N k) (gaussianMatrix (Fin N) (Fin k)) μ := by
  sorry

/-- **Consecutive draws are independent**: if the tape $x$ is an i.i.d. sequence with a
probability law $\nu$, the $N \times k$ matrix drawn from position $0$ and the $N \times \ell$
matrix drawn after it, from position $Nk$, are independent. No printed source.
Result: tape-independent-draws -/
theorem indepFun_tapeMatrix_of_hasLaw_iidSequence {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {x : Ω → ℕ → ℝ} (hx : HasLaw x (iidSequence ν) μ) (N k ℓ : ℕ) :
    IndepFun (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) 0 N k)
      (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) (N * k) N ℓ) μ := by
  sorry

end NLAlib
