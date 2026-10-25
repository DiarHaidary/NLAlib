/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Data.Multiset.Sort

/-!
# Rolle's theorem for zeros counted with multiplicity

If $f$ has $q + 2$ zeros counted with multiplicity in $[a, b]$, a zero of multiplicity $r$ at $y$
meaning that $f, f', \dots, f^{(r-1)}$ vanish at $y$, then $f^{(q+1)}$ vanishes somewhere in
$(a, b)$. Repeated zeros must be interior; simple zeros may sit at the endpoints, where only
continuity is used. This is the step behind every Hermite interpolation remainder (Gauss nodes
doubled, Radau and Lobatto endpoints simple). Mathlib has the single-derivative case
`exists_deriv_eq_zero`. Upstream candidate for `Mathlib.Analysis.Calculus.LocalExtr.Rolle`.

Design: stage KS8 (`docs/design/Polynomial-QuadratureRemainder.md`, F3).

## Main results

* `exists_iteratedDeriv_eq_zero_of_multiset`: iterated Rolle with multiplicities.
-/

@[expose] public section

open Set

/-- **Rolle's theorem with multiplicities**: let $m$ be a multiset of $q + 2$ points of
$[a, b]$, every point of multiplicity at least $2$ in $(a, b)$, and let $f$ be continuous on
$[a, b]$ and $C^{q+1}$ on $(a, b)$ with $f^{(j)}(y) = 0$ for every $y \in m$ and every $j$ below
the multiplicity of $y$. Then $f^{(q+1)}(\xi) = 0$ for some $\xi \in (a, b)$.
[Davis1975, Theorem 1.6.3] (locator to check); there for distinct zeros of $f$.
Proof: L, about 180 lines; the prototype proves it
(`exists_iteratedDeriv_eq_zero_of_multiset_multiplicities` with the private
`exists_iteratedDeriv_eq_zero_of_monotone_with_multiplicities`,
`NLAlib/ForMathlib/Analysis/Calculus/RolleMultiplicity.lean`): sort $m$ into a monotone
`Fin (q + 2)` family (`Multiset.sort`), apply `exists_deriv_eq_zero` between consecutive
distinct entries and keep repeated entries, which gives $q + 1$ zeros of $f'$ with the
multiplicities shifted down by one, and induct on $q$. The all-equal case needs no Rolle step:
then the single point has multiplicity $q + 2 > 1$, so it is interior and `hz` gives the
conclusion at it (the prototype's extra hypothesis that two points differ is not needed).
`ContDiffOn` on the open interval gives `DifferentiableOn` of `iteratedDeriv j f` for $j \le q$
(`ContDiffOn.differentiableOn_iteratedDerivWithin` with `iteratedDerivWithin_of_isOpen`). -/
theorem exists_iteratedDeriv_eq_zero_of_multiset {f : ℝ → ℝ} {a b : ℝ} {m : Multiset ℝ} {q : ℕ}
    (hm : m.card = q + 2) (hmem : ∀ y ∈ m, y ∈ Icc a b)
    (hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Ioo a b) (hf : ContinuousOn f (Icc a b))
    (hf' : ContDiffOn ℝ (q + 1 : ℕ) f (Ioo a b))
    (hz : ∀ y ∈ m, ∀ j < m.count y, iteratedDeriv j f y = 0) :
    ∃ ξ ∈ Ioo a b, iteratedDeriv (q + 1) f ξ = 0 := by
  sorry
