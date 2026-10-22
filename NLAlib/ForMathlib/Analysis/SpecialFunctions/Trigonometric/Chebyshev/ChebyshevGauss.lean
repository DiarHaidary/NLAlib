/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
-- for the body of `Polynomial.Chebyshev.sumZeroes`, which Mathlib does not expose
import all Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss

/-!
# Chebyshev–Gauss: the defining sum

Mathlib's `Polynomial.Chebyshev.sumZeroes` is a definition whose body is not exposed to
importing modules, and Mathlib states no lemma giving its value. This file states it, so that
Chebyshev–Gauss quadrature (`Polynomial.Chebyshev.integral_eq_sumZeroes`) can be read as an
explicit sum over the nodes. It is an upstream candidate in
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss`.

## Main results

* `Polynomial.Chebyshev.sumZeroes_def`: the weighted sum over the zeros of $T_n$.
-/

@[expose] public section

namespace Polynomial.Chebyshev

/-- The value of `sumZeroes`: $(\pi/n)\sum_{i<n}P(\cos((2i + 1)\pi/(2n)))$. -/
theorem sumZeroes_def (n : ℕ) (P : ℝ[X]) :
    sumZeroes n P =
      Real.pi / n * ∑ i ∈ Finset.range n, P.eval (Real.cos ((2 * i + 1) / (2 * n) * Real.pi)) := by
  rw [sumZeroes]

end Polynomial.Chebyshev
