/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Gauss
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# The Gauss rule and the minimax error: the theorems of stage Poly-Best

Statements for `NLAlib/Polynomial/Orthogonal/Gauss.lean` whose proofs are deferred
(`docs/design/Polynomial-BestApproximation.md`, §3.4): the error of the $(k + 1)$-point Gauss
rule restated with the minimax error in degree $2k + 1$.

## Main results

* `NLAlib.abs_integral_sub_integral_gaussQuadrature_le_of_continuousOn`: the bound
  $2E_{2k + 1}(f)\mu(\mathbb{R})$.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- **The Gauss-rule error and the minimax error**: for a finite measure $\mu$ supported in
$[a, b]$ and $f$ continuous on $[a, b]$, the $(k + 1)$-point Gauss rule satisfies
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k + 1)\Bigr\rvert \le
2E_{2k + 1}(f; [a, b])\,\mu(\mathbb{R})\,,$$
$E_{2k + 1}$ the error of the best uniform approximation of $f$ on $[a, b]$ by polynomials of
degree at most $2k + 1$ (`minimaxError`). [GolubMeurant2010, Ch. 6]; [Trefethen2019, Ch. 19]
(locator to check).
Proof: S, about 10 lines. Integrability of $f$ from `ContinuousOn.integrableOn_Icc` and
`Measure.restrict_eq_self_of_ae_mem` (as in
`abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith`);
`exists_degree_le_isUniformApproxOn_minimaxError` in degree $2k + 1 < 2(k + 1)$; then
`abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn`. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_continuousOn
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) (k : ℕ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ (k + 1)| ≤
      2 * minimaxError f (Set.Icc a b) (2 * k + 1) * μ.real Set.univ := by
  sorry

end NLAlib
