/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Polynomial.Orthogonal.Basic

/-!
# Gauss quadrature

The interpolatory quadrature rule of a measure $\mu$ at distinct nodes $s \subseteq \mathbb{R}$
puts at each node $x$ the weight $\int\ell_x\,d\mu$, $\ell_x$ the Lagrange basis polynomial of
$x$ (Mathlib's `Lagrange.basis s id x`); it integrates every polynomial of degree less than
$\lvert s\rvert$ exactly. When the nodal polynomial $\pi_s(z) = \prod_{x\in s}(z - x)$ is
orthogonal to the polynomials of degree less than $\lvert s\rvert$ (the nodes are the zeros of
the degree-$\lvert s\rvert$ orthogonal polynomial of $\mu$), it is the Gauss rule: its weights
are nonnegative, $\int\ell_x\,d\mu = \int\ell_x^2\,d\mu$, and it integrates every polynomial of
degree less than $2\lvert s\rvert$ exactly, so it matches the first $2\lvert s\rvert$ moments of
$\mu$.

The existence of Gauss nodes for a given measure (the orthogonal polynomial has real, distinct
zeros inside the support) is not proved here. For spectral measures the Ritz values of the
Lanczos method supply them (`NLAlib.HasOrthonormalCols.isOrthogonalPolynomial_nodal`).

## Main definitions

* `NLAlib.interpolatoryQuadrature`: the interpolatory rule as a measure.

## Main results

* `NLAlib.IsOrthogonalPolynomial.integral_eval_eq_sum`: Gauss quadrature is exact through degree
  $2\lvert s\rvert - 1$.
* `NLAlib.IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq`: the weights are
  nonnegative.
* `NLAlib.IsOrthogonalPolynomial.matchesMoments_interpolatoryQuadrature`: the rule matches
  $2\lvert s\rvert$ moments.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- The **interpolatory quadrature rule** of $\mu$ at the nodes $s$, as a measure: weight
$\int \ell_x\,d\mu$ at each node $x$, $\ell_x$ the Lagrange basis polynomial. At Gauss nodes the
weights are nonnegative (`IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq`), and the
rule is the Gauss rule. Junk: negative weights are truncated at $0$, so at nodes that are not
Gauss nodes the measure need not be the interpolatory rule. -/
noncomputable def interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) : Measure ℝ :=
  ∑ x ∈ s, ENNReal.ofReal (∫ t, (Lagrange.basis s id x).eval t ∂μ) • Measure.dirac x

/-- An interpolatory quadrature rule is a finite measure. -/
instance isFiniteMeasure_interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) :
    IsFiniteMeasure (interpolatoryQuadrature μ s) := by
  unfold interpolatoryQuadrature
  have : ∀ x : ℝ, IsFiniteMeasure (ENNReal.ofReal (∫ t, (Lagrange.basis s id x).eval t ∂μ) •
      Measure.dirac x) := fun x => Measure.smul_finite _ ENNReal.ofReal_ne_top
  infer_instance

/-- **Gauss quadrature**: if the nodal polynomial $\pi_s$ of distinct real nodes $s$ is
orthogonal in $L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite
measure $\mu$ supported in $[a, b]$, then
$$\int p\,d\mu = \sum_{x\in s}\Bigl(\int\ell_x\,d\mu\Bigr)p(x)$$
for every real polynomial $p$ of degree less than $2\lvert s\rvert$, $\ell_x$ the Lagrange basis
polynomial of $x$. [Gautschi2004, Theorems 1.45 and 1.46]; [GolubMeurant2010, Theorem 6.6];
there at the zeros of the orthogonal polynomial of a positive measure; here at any nodes whose
nodal polynomial is orthogonal.
Result: gauss-quadrature -/
theorem IsOrthogonalPolynomial.integral_eval_eq_sum {μ : Measure ℝ} {s : Finset ℝ}
    (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id)) [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : p.degree < 2 * s.card) :
    ∫ x, p.eval x ∂μ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * p.eval x := by
  sorry

/-- The Gauss weights are nonnegative: if the nodal polynomial of $s$ is orthogonal in
$L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite measure $\mu$
supported in $[a, b]$, then the weight of each node $x \in s$ is
$\int\ell_x\,d\mu = \int\ell_x^2\,d\mu \ge 0$, $\ell_x$ the Lagrange basis polynomial of $x$:
$\ell_x^2 - \ell_x$ vanishes at the nodes and has degree less than $2\lvert s\rvert$. -/
theorem IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x : ℝ} (hx : x ∈ s) :
    ∫ t, (Lagrange.basis s id x).eval t ∂μ = ∫ t, (Lagrange.basis s id x).eval t ^ 2 ∂μ := by
  sorry

/-- **The Gauss rule matches $2\lvert s\rvert$ moments**: if the nodal polynomial of $s$ is
orthogonal in $L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite
measure $\mu$ supported in $[a, b]$, then $\mu$ and its interpolatory rule at $s$ match their
first $2\lvert s\rvert$ moments.
[Gautschi2004, Theorems 1.45 and 1.46]; [GolubMeurant2010, Theorem 6.6].
Result: gauss-quadrature -/
theorem IsOrthogonalPolynomial.matchesMoments_interpolatoryQuadrature {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    MatchesMoments μ (interpolatoryQuadrature μ s) (2 * s.card) := by
  sorry

/-- The integral against the Gauss rule: if the nodal polynomial of $s$ is orthogonal in
$L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite measure $\mu$
supported in $[a, b]$, then for every $f : \mathbb{R} \to \mathbb{R}$ the integral of $f$ against
the interpolatory rule at $s$ is $\sum_{x\in s}\bigl(\int\ell_x\,d\mu\bigr)f(x)$, $\ell_x$ the
Lagrange basis polynomial of $x$; the truncation of the weights at $0$ does not act. -/
theorem IsOrthogonalPolynomial.integral_interpolatoryQuadrature {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (f : ℝ → ℝ) :
    ∫ x, f x ∂interpolatoryQuadrature μ s =
      ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * f x := by
  sorry

end NLAlib
