/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Iterated derivatives of polynomial functions

The iterated derivative of $x \mapsto p(x)$ is the evaluation of the iterated formal derivative
of $p$: the bridge between the analytic jets of an interpolation remainder and the algebraic
jets of the interpolant. Mathlib has the first derivative, `Polynomial.deriv`. Upstream candidate
for `Mathlib.Analysis.Calculus.Deriv.Polynomial`, next to `Polynomial.deriv`.


## Main results

* `Polynomial.iteratedDeriv`: $(d/dx)^k\,p(x) = p^{(k)}(x)$.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The iterated derivative of a polynomial function: for every polynomial $p$ over $\Bbbk$,
every $k$ and every $x$, the $k$-th derivative of $x \mapsto p(x)$ at $x$ is $p^{(k)}(x)$, the
$k$-th formal derivative evaluated at $x$. -/
protected theorem iteratedDeriv (p : 𝕜[X]) (k : ℕ) (x : 𝕜) :
    iteratedDeriv k (fun x => p.eval x) x = (derivative^[k] p).eval x := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have hf : deriv (fun x : 𝕜 => p.eval x) = fun x => (derivative p).eval x :=
      funext fun y => Polynomial.deriv p
    rw [hf, ih]

end Polynomial
