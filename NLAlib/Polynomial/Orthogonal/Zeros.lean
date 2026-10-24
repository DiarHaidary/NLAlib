/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Recurrence

/-!
# Zeros of orthogonal polynomials

The Gauss nodes of order $k$ of a measure $\mu$ on $\mathbb{R}$ are the distinct real zeros of
its monic orthogonal polynomial $\pi_k$ (`NLAlib.orthogonalPolynomial`). When $\mu$, finite and
supported in $[a, b]$, is positive definite up to degree $k$, $\pi_k$ has $k$ real simple zeros
in $[a, b]$ and is their nodal polynomial; otherwise $\mu$ is carried by the zeros of $\pi_k$.
In both cases the nodal polynomial of the Gauss nodes is orthogonal to the polynomials of lower
degree, the hypothesis of Gauss quadrature (`NLAlib.Polynomial.Orthogonal.Gauss`).
[Gautschi2004]; [Szego1975].

## Main definitions

* `NLAlib.gaussNodes`: the distinct real zeros of $\pi_k$.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- The **Gauss nodes** of order $k$: the distinct real zeros of $\pi_k$. When $\mu$ is positive
definite up to degree $k$ there are $k$ of them, in every interval carrying $\mu$, and
$\pi_k$ is their nodal polynomial. Junk: past the number of support points, the support and
possibly $0$. -/
noncomputable def gaussNodes (μ : Measure ℝ) (k : ℕ) : Finset ℝ :=
  (orthogonalPolynomial μ k).roots.toFinset

end NLAlib
