/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import NLAlib.Polynomial.Orthogonal.Basic

/-!
# The three-term recurrence of orthogonal polynomials

The monic orthogonal polynomials $\pi_0, \pi_1, \dots$ of a measure $\mu$ on $\mathbb{R}$, defined
by the Stieltjes procedure: $\pi_0 = 1$, $\pi_1 = x - \alpha_0$ and
$$\pi_{k+2} = (x - \alpha_{k+1})\pi_{k+1} - \beta_{k+1}\pi_k\,,$$
with $\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$ and
$\beta_k = \int\pi_k^2\,d\mu/\int\pi_{k-1}^2\,d\mu$, $\beta_0 = \mu(\mathbb{R})$ (Gautschi's
convention). The recurrence is the definition, so it holds by `rfl`; orthogonality, uniqueness
and moment invariance are theorems. The definitions are total: a zero norm gives a zero
coefficient (Lean's $x/0 = 0$), $\pi_k$ is monic of degree $k$ for every measure, and for a measure
with $N$ support points $\pi_N$ is the nodal polynomial of the support and every later $\pi_k$ a
multiple of it.

The Jacobi matrix of order $k$ carries $\alpha_0, \dots, \alpha_{k-1}$ on its diagonal and
$\sqrt{\beta_1}, \dots, \sqrt{\beta_{k-1}}$ beside it, in the layout of the Lanczos tridiagonal
matrix. [Gautschi2004]; [Szego1975].

## Main definitions

* `NLAlib.orthogonalPolynomial`: the monic orthogonal polynomials, by the Stieltjes recurrence.
* `NLAlib.jacobiAlpha`, `NLAlib.jacobiBeta`: the recurrence coefficients.
* `NLAlib.jacobiMatrix`: the Jacobi matrix.

## Main results

* `NLAlib.orthogonalPolynomial_add_two`: the three-term recurrence (by definition).
* `NLAlib.orthogonalPolynomial_zero`, `NLAlib.orthogonalPolynomial_one`,
  `NLAlib.jacobiBeta_zero`: the initial values.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- The **monic orthogonal polynomials** of $\mu$, by the Stieltjes procedure:
$\pi_0 = 1$, $\pi_1 = x - \alpha_0$ and
$\pi_{k+2} = (x - \alpha_{k+1})\pi_{k+1} - \beta_{k+1}\pi_k$, with
$\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$ and
$\beta_k = \int\pi_k^2\,d\mu/\int\pi_{k-1}^2\,d\mu$ (`jacobiAlpha`, `jacobiBeta`).
$\pi_k$ is monic of degree $k$ for every $\mu$ and $k$. For a finite measure with compact support
it is orthogonal to every polynomial of degree less than $k$
(`isOrthogonalPolynomial_orthogonalPolynomial`), and it is the only monic such polynomial of
degree $k$ when $\mu$ is positive definite up to degree $k$
(`IsMomentPosDef.eq_orthogonalPolynomial`). Junk: a zero norm gives a zero coefficient
($x/0 = 0$); for a measure with $N$ support points, $\pi_N$ is the nodal polynomial of the support
and every later $\pi_k$ is a multiple of it. [Gautschi2004, Theorem 1.27]. -/
noncomputable def orthogonalPolynomial (μ : Measure ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - C ((∫ x, x * (1 : ℝ[X]).eval x ^ 2 ∂μ) / ∫ x, (1 : ℝ[X]).eval x ^ 2 ∂μ)
  | k + 2 =>
    (X - C ((∫ x, x * (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ)) * orthogonalPolynomial μ (k + 1) -
      C ((∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ) * orthogonalPolynomial μ k

/-- The **diagonal recurrence coefficient** $\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$;
$0$ when $\pi_k$ has norm $0$. -/
noncomputable def jacobiAlpha (μ : Measure ℝ) (k : ℕ) : ℝ :=
  (∫ x, x * (orthogonalPolynomial μ k).eval x ^ 2 ∂μ) /
    ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ

/-- The **off-diagonal recurrence coefficient** $\beta_k = \int\pi_k^2\,d\mu/
\int\pi_{k-1}^2\,d\mu$ for $k \ge 1$, and $\beta_0 = \mu(\mathbb{R})$ (Gautschi's convention);
$0$ when $\pi_{k-1}$ has norm $0$. The Jacobi matrix carries $\sqrt{\beta_k}$. -/
noncomputable def jacobiBeta (μ : Measure ℝ) : ℕ → ℝ
  | 0 => μ.real Set.univ
  | k + 1 => (∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
      ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ

/-- The **Jacobi matrix** of order $k$: $\alpha_0, \dots, \alpha_{k-1}$ on the diagonal,
$\sqrt{\beta_1}, \dots, \sqrt{\beta_{k-1}}$ beside it; the same layout as `lanczosTridiagonal`. -/
noncomputable def jacobiMatrix (μ : Measure ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then jacobiAlpha μ i
    else if (i : ℕ) = j + 1 then √(jacobiBeta μ i)
    else if (j : ℕ) = i + 1 then √(jacobiBeta μ j)
    else 0

/-- The orthogonal polynomial of degree $0$ is $\pi_0 = 1$, by definition. -/
theorem orthogonalPolynomial_zero (μ : Measure ℝ) : orthogonalPolynomial μ 0 = 1 := rfl

/-- The orthogonal polynomial of degree $1$ is $\pi_1 = x - \alpha_0$, by definition. -/
theorem orthogonalPolynomial_one (μ : Measure ℝ) :
    orthogonalPolynomial μ 1 = X - C (jacobiAlpha μ 0) := rfl

/-- **The three-term recurrence**: for every measure $\mu$ on $\mathbb{R}$ and every $k$,
$$\pi_{k+2} = (x - \alpha_{k+1})\pi_{k+1} - \beta_{k+1}\pi_k\,,$$
with $\alpha_k = \int x\pi_k^2\,d\mu/\int\pi_k^2\,d\mu$ and
$\beta_k = \int\pi_k^2\,d\mu/\int\pi_{k-1}^2\,d\mu$ (zero when the denominator is).
[Gautschi2004, Theorem 1.27]; [Szego1975, Theorem 3.2.1] (locator to check); there as a theorem
about the orthogonal polynomials, here the definition.
Result: orthogonal-polynomial-recurrence -/
theorem orthogonalPolynomial_add_two (μ : Measure ℝ) (k : ℕ) :
    orthogonalPolynomial μ (k + 2) =
      (X - C (jacobiAlpha μ (k + 1))) * orthogonalPolynomial μ (k + 1) -
        C (jacobiBeta μ (k + 1)) * orthogonalPolynomial μ k := rfl

/-- The first off-diagonal coefficient is the mass, $\beta_0 = \mu(\mathbb{R})$, by
definition. -/
theorem jacobiBeta_zero (μ : Measure ℝ) : jacobiBeta μ 0 = μ.real Set.univ := rfl

end NLAlib
