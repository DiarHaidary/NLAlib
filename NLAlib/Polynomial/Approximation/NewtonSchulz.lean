/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The Newton–Schulz iteration for the sign function

The cubic $g(x) = \tfrac12 x(3 - x^2)$ (`NLAlib.newtonSchulz`) fixes $-1$, $0$ and $1$, with
$g'(\pm 1) = 0$; iterated from a point of $(-\sqrt 5, \sqrt 5)$ other than $0$ it converges
quadratically to the sign of the point, and an iteration perturbed by an error of size $u$ at
each step still reaches $\lvert 1 - x^2 \rvert \le \varepsilon$ after
`NLAlib.newtonSchulzSteps` $x_0$ $\varepsilon$ steps, about
$2\log_2(1/\lvert x_0 \rvert) + \log_2\log_2(1/\varepsilon)$ ([Shah2024, Section 2]). Applied to a
Hermitian matrix through the functional calculus it is the inverse-free iteration for the matrix
sign function.

## Main definitions

* `NLAlib.newtonSchulz`: the cubic $g$.
* `NLAlib.newtonSchulzSteps`: the step count of the perturbed scalar iteration.

## Main results

The scalar convergence theorems are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` (stage HDIAG).
-/

@[expose] public section

namespace NLAlib

/-- The **Newton–Schulz map** $g(x) = \tfrac12 x(3 - x^2)$, Newton's method for
$x^{-2} - 1 = 0$. [Shah2024, Section 2.1].
Algorithm: newton-schulz-sign -/
noncomputable def newtonSchulz (x : ℝ) : ℝ :=
  x * (3 - x ^ 2) / 2

/-- The **step count of the perturbed Newton–Schulz iteration** from $x_0$ to tolerance
$\varepsilon$:
$$N(x_0, \varepsilon) = \frac52 + 2\log_2\frac{1}{\min(\lvert x_0 \rvert, 1/2)} +
\log_2\log_2\frac{1}{\varepsilon} \,,$$
a real number; the iteration count is any natural number at least this value. Junk values: at
$x_0 = 0$ the middle term is $0$ (Mathlib's $0^{-1} = 0$), and the last term is $0$ unless
$\varepsilon < 1/2$. [Shah2024, Lemma 2.5], the quantity $N_{\mathrm{SCALAR}}$ there. -/
noncomputable def newtonSchulzSteps (x₀ ε : ℝ) : ℝ :=
  5 / 2 + 2 * Real.logb 2 (min |x₀| (1 / 2))⁻¹ + Real.logb 2 (Real.logb 2 ε⁻¹)

end NLAlib
