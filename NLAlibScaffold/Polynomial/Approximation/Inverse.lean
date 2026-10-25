/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.Inverse
public import NLAlibScaffold.Polynomial.Approximation.MinimaxError

/-!
# The minimax error of the inverse: the theorems of stage Poly-Best

Statements for `NLAlib/Polynomial/Approximation/Inverse.lean` whose proofs are deferred
(`docs/design/Polynomial-BestApproximation.md`, §3.4): the Chebyshev upper bound on
$E_n(x^{-1}; [a, b])$.

## Main results

* `NLAlib.minimaxError_inv_le`: $E_n(x^{-1}; [a, b])$ decays like the CG rate.
-/

@[expose] public section

open Real

namespace NLAlib

/-- **The minimax error of the inverse**: for $0 < a < b$,
$$E_n\bigl(x^{-1}; [a, b]\bigr) \le \frac2a
\left(\frac{\sqrt b - \sqrt a}{\sqrt b + \sqrt a}\right)^{n + 1}\,.$$
The matching lower bound (the exact value of $E_n(x^{-1})$) is deferred. A corollary of
[Saad2003, Theorem 6.25 and proof of Theorem 6.29].
Proof: S, about 6 lines. `exists_degree_lt_isUniformApproxOn_inv` at $q = n + 1$
(`Order.lt_add_one_iff` on `WithBot ℕ`, or `Nat.cast_lt` with `degree_le_of_lt`), then
`minimaxError_le_of_isUniformApproxOn` (`positivity`).
Result: inverse-polynomial-approx -/
theorem minimaxError_inv_le {a b : ℝ} (n : ℕ) (ha : 0 < a) (hab : a < b) :
    minimaxError (fun x => x⁻¹) (Set.Icc a b) n ≤
      (2 / a) * ((√b - √a) / (√b + √a)) ^ (n + 1) := by
  obtain ⟨p, hp, hε⟩ := exists_degree_lt_isUniformApproxOn_inv (n + 1) ha hab
  have hdeg : p.degree ≤ n := by
    have h : p.degree < ((n + 1 : ℕ) : WithBot ℕ) := hp
    exact Order.le_of_lt_succ (by exact_mod_cast h)
  exact minimaxError_le_of_isUniformApproxOn hdeg (hε.nonneg (Set.nonempty_Icc.mpr hab.le)) hε

end NLAlib
