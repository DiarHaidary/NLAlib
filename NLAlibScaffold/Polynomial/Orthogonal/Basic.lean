/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Polynomial.Orthogonal.Basic
public import NLAlibScaffold.Polynomial.Orthogonal.Moments

/-!
# Positive definiteness up to a degree: the API of stage KS7

Statements for `NLAlib/Polynomial/Orthogonal/Basic.lean` whose proofs are deferred
(`docs/design/Polynomial-OrthogonalStructure.md`, §4.2). Positive definiteness on the polynomials
of degree less than $k$ (`NLAlib.IsMomentPosDef`) is monotone in $k$, and for a finite measure
with compact support it says that no finite set of fewer than $k$ points carries the measure.

## Main results

* `NLAlib.IsMomentPosDef.mono`: definiteness up to a lower degree.
* `NLAlib.isMomentPosDef_iff_forall_finset`: definiteness counts support points.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- Positive definiteness on the polynomials of degree less than $k$ gives it on those of degree
less than $j \le k$.
Proof: S, about 5 lines. As `IsOrthogonalPolynomial.mono`: `h p hp (hdeg.trans_le …)` with
`exact_mod_cast hjk`. -/
theorem IsMomentPosDef.mono {μ : Measure ℝ} {j k : ℕ} (h : IsMomentPosDef μ k) (hjk : j ≤ k) :
    IsMomentPosDef μ j :=
  fun p hp hpdeg => h p hp (hpdeg.trans_le (by exact_mod_cast hjk))

/-- **Positive definiteness counts support points**: a finite measure $\mu$ supported in
$[a, b]$ is positive definite on the polynomials of degree less than $k$ exactly when no finite
set of fewer than $k$ points carries it: every finite $s$ with $x \in s$ for $\mu$-almost every
$x$ has $k \le \lvert s\rvert$. [Gautschi2004, §1.1] (locator to check).
Proof: M, about 35 lines. ⇒: a set $s$ carrying $\mu$ with $\lvert s\rvert < k$ gives the nonzero
`Lagrange.nodal s id` (degree $\lvert s\rvert$, `Lagrange.degree_nodal`) of norm $0$
(`integral_eq_zero_of_ae`, `Lagrange.eval_nodal_at_node`). ⇐: a nonzero $p$ of degree $< k$ and
norm $0$ vanishes a.e. (`ae_eval_eq_zero_of_integral_sq_eq_zero`), so $\mu$ is carried by
`p.roots.toFinset`, of card $\le \deg p < k$ (`Multiset.toFinset_card_le`, `card_roots'`,
`mem_roots`); the norm is nonnegative (`integral_nonneg`). -/
theorem isMomentPosDef_iff_forall_finset {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsMomentPosDef μ k ↔ ∀ s : Finset ℝ, (∀ᵐ x ∂μ, x ∈ s) → k ≤ s.card := by
  sorry

end NLAlib
