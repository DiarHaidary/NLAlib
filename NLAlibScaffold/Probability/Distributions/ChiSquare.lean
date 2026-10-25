/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquare
public import NLAlibScaffold.ForMathlib.Probability.Distributions.ChiSquared

/-!
# The law of the squared norm of a standard Gaussian vector

Statements for `NLAlib/Probability/Distributions/ChiSquare.lean` whose proofs are deferred
(`docs/design/Probability-Beta.md`, §3.1, β1′). For a standard Gaussian vector $\mathbf{g}$ in
$\mathbb{R}^n$, $n$ nonempty, $\|\mathbf{g}\|^2$ has the chi-square law $\chi^2_d$ with
$d = \lvert n \rvert$, Mathlib's `gammaMeasure (d / 2) (1 / 2)`: the law behind the Laplace
transforms and tails of `NLAlib/Probability/Distributions/ChiSquare.lean`.

## Main results

* `NLAlib.hasLaw_norm_sq_of_hasLaw_gaussianVector`: the chi-square law of $\|\mathbf{g}\|^2$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]

/-- **The squared norm of a standard Gaussian vector is chi-square**: for $\mathbf{g}$ with law
`gaussianVector n` (independent standard normal coordinates) and $n$ nonempty,
$\|\mathbf{g}\|^2$ has law $\mathrm{Gamma}(d/2, 1/2)$ with $d = \lvert n \rvert$ (shape $d/2$,
rate $1/2$), the chi-square law with $d$ degrees of freedom.
Proof: S, about 3 lines. `(hasLaw_sum_sq_of_hasLaw_pi_gaussianReal hg).congr
(ae_of_all _ fun ω => by simp [EuclideanSpace.real_norm_sq_eq])` (checked against the
statements; `gaussianVector` is an `abbrev` of the product law). -/
theorem hasLaw_norm_sq_of_hasLaw_gaussianVector {g : Ω → n → ℝ} [Nonempty n]
    (hg : HasLaw g (gaussianVector n) μ) :
    HasLaw (fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2) (gammaMeasure (Fintype.card n / 2) (1 / 2)) μ :=
  (hasLaw_sum_sq_of_hasLaw_pi_gaussianReal hg).congr
    (ae_of_all _ fun ω => by simp [EuclideanSpace.real_norm_sq_eq])

end NLAlib
