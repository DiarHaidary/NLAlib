/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation

/-!
# The minimax error of polynomial approximation

The best uniform error $E_n(f; s)$ of approximating a real function $f$ on a set
$s \subseteq \mathbb{R}$ by real polynomials of degree at most $n$. The theorems (existence of a
best approximant, the basic algebra of $E_n$, affine change of interval, Weierstrass) are in the
scaffold until proved (`docs/design/Polynomial-BestApproximation.md`).

## Main definitions

* `NLAlib.minimaxError`: $E_n(f; s)$.
-/

@[expose] public section

open Polynomial

namespace NLAlib

/-- The **minimax error** of $f$ on $s$ at degree $n$,
$$E_n(f; s) := \inf\bigl\{\varepsilon : \exists p \in \mathbb{R}[x],\ \deg p \le n,\
\lvert f(x) - p(x) \rvert \le \varepsilon \text{ for all } x \in s\bigr\},$$
the error of the best uniform approximation of $f$ on $s$ by real polynomials of degree at most
$n$, through the library's uniform-approximation interface `Metric.IsUniformApproxOn`.
Junk values: $0$ when no polynomial of degree at most $n$ is within a finite distance of $f$ on
$s$ (the set is empty; for example $f$ unbounded on a bounded $s$), and $0$ for $s = \emptyset$
(the set is all of $\mathbb{R}$). It is meaningful whenever some polynomial of degree at most $n$
is within a finite distance of $f$ on $s$, in particular for $s$ compact and $f$ continuous on
$s$, where the infimum is attained. [Trefethen2019, Ch. 10]; [Rivlin1981, Ch. 1]. -/
noncomputable def minimaxError (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) : ℝ :=
  sInf {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
    Metric.IsUniformApproxOn (fun x => p.eval x) f s ε}

end NLAlib
