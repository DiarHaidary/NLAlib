/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Zeros

/-!
# The Gauss nodes are interior: the theorems of stage KS8

Statements for `NLAlib/Polynomial/Orthogonal/Zeros.lean` whose proofs are deferred
(`docs/design/Polynomial-QuadratureRemainder.md`, Z1). If a finite measure supported in $[a, b]$
has more than $k$ support points, the zeros of its orthogonal polynomial $\pi_k$ lie in the open
interval $(a, b)$; with exactly $k$ support points they are the support points and may sit at
$a$ or $b$.

## Main results

* `NLAlib.IsMomentPosDef.gaussNodes_subset_Ioo`: interior Gauss nodes.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- **The Gauss nodes are interior**: if a finite measure $\mu$ supported in $[a, b]$ is positive
definite up to degree $k + 1$ (it has more than $k$ support points), then every zero of the
orthogonal polynomial $\pi_k$ lies in $(a, b)$. Definiteness up to degree $k$ is not enough:
$\mu = \delta_a + \delta_b$ has $\pi_2 = (x - a)(x - b)$. [Gautschi2004, Theorem 1.19];
[Szego1975, Theorem 3.3.1] (locators to check); there in the interior of the support interval.
Proof: M, about 40 lines. By `IsMomentPosDef.gaussNodes_subset_Icc` (from `h.mono`) the zeros lie
in $[a, b]$; suppose $\pi_k(a) = 0$ (the case $b$ is symmetric), so $\pi_k = (x - a)r$ with
$\deg r = k - 1$ (`mul_divByMonic_eq_iff_isRoot`). Orthogonality
(`isOrthogonalPolynomial_orthogonalPolynomial`) gives
$0 = \int\pi_k r\,d\mu = \int(x - a)r^2\,d\mu$ with a nonnegative integrand on $[a, b]$, so
$(x - a)r^2 = 0$ a.e. (`integral_eq_zero_iff_of_nonneg_ae`), hence
$\int((x - a)r)^2\,d\mu = \int(x - a)\cdot(x - a)r^2\,d\mu = 0$, contradicting definiteness at
the nonzero $\pi_k = (x - a)r$ of degree $k < k + 1$. -/
theorem IsMomentPosDef.gaussNodes_subset_Ioo {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    {k : ℕ} (h : IsMomentPosDef μ (k + 1)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    (gaussNodes μ k : Set ℝ) ⊆ Set.Ioo a b := by
  sorry

end NLAlib
