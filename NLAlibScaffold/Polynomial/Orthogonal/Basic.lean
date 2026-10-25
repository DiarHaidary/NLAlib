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
  constructor
  · -- the nodal polynomial of a carrying set of fewer than `k` points has norm zero
    intro h s hs
    by_contra! hlt
    have hdeg : (Lagrange.nodal s id).degree < k := by
      rw [Lagrange.degree_nodal]
      exact_mod_cast hlt
    refine (h _ Lagrange.nodal_ne_zero hdeg).ne' ?_
    exact integral_eq_zero_of_ae <| hs.mono fun x hx =>
      (pow_eq_zero_iff two_ne_zero).mpr (Lagrange.eval_nodal_at_node (v := id) hx)
  · -- a polynomial of norm zero vanishes off its roots, which are fewer than `k`
    intro h p hp0 hpdeg
    refine (integral_nonneg fun x => sq_nonneg _).lt_of_ne' fun h0 => ?_
    have h1 := h _ <| (ae_eval_eq_zero_of_integral_sq_eq_zero hμ h0).mono fun x hx =>
      Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr hx)
    have h2 := (Multiset.toFinset_card_le p.roots).trans (card_roots' p)
    have h3 := (natDegree_lt_iff_degree_lt hp0).mpr hpdeg
    omega

end NLAlib
