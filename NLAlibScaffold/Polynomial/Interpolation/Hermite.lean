/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import NLAlibScaffold.ForMathlib.Algebra.Polynomial.Derivative
public import NLAlibScaffold.ForMathlib.Analysis.Calculus.Deriv.Polynomial
public import NLAlibScaffold.ForMathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Hermite interpolation and the interpolation remainder

Nodes with multiplicity are a multiset $m$: a node $y$ of multiplicity $r$ prescribes the values
$p(y), p'(y), \dots, p^{(r-1)}(y)$. For any such data there is exactly one polynomial of degree
less than $\lvert m\rvert$ matching it (confluent Hermite interpolation). If $f$ is smooth and
$H$ matches the jets of $f$, the error is
$$f(x) - H(x) = \frac{f^{(\lvert m\rvert)}(\xi)}{\lvert m\rvert!}\,\omega_m(x)\,,\qquad
\omega_m = \prod_{y\in m}(x - y)\,,$$
for some $\xi$ in the interval. Simple nodes give the Lagrange interpolation remainder for
Mathlib's `Lagrange.interpolate`; doubled Gauss nodes and simple endpoints give the Gauss, Radau
and Lobatto remainders (`NLAlib.Polynomial.Orthogonal.Gauss`,
`NLAlib.Polynomial.Orthogonal.RadauLobatto`).

There is no Hermite interpolant definition: the remainder is stated for any polynomial matching
the jets, and the existence theorem supplies one (`docs/design/Polynomial-QuadratureRemainder.md`,
OQ1).

## Main results

* `NLAlib.exists_degree_lt_forall_iterate_derivative_eval_eq`: existence of the Hermite
  interpolant.
* `NLAlib.eq_of_degree_lt_of_forall_iterate_derivative_eval_eq`: its uniqueness.
* `NLAlib.exists_sub_eval_eq_iteratedDeriv_mul`: the Hermite interpolation remainder.
* `NLAlib.exists_sub_eval_interpolate_eq_iteratedDeriv_mul`: the Lagrange interpolation
  remainder.
-/

@[expose] public section

open Polynomial

namespace NLAlib

/-! ### Existence and uniqueness -/

section Algebra

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

/-- **Uniqueness of Hermite interpolation**: over a field of characteristic $0$, two polynomials
of degree less than $\lvert m\rvert$ whose derivatives of order below the multiplicity of $y$
agree at every $y$ of the multiset $m$ are equal.
[Davis1975, Theorem 2.7.1] (locator to check).
Proof: M, about 30 lines. Let $d = p - q$ (`iterate_derivative_sub`). If $d \ne 0$, every
$y \in m$ has `rootMultiplicity y d ≥ count y m`
(`lt_rootMultiplicity_iff_isRoot_iterate_derivative`, characteristic $0$), so
$m \le d.\mathrm{roots}$ (`Multiset.le_iff_count`, `count_roots`) and
$\lvert m\rvert \le \deg d < \lvert m\rvert$ (`Multiset.card_le_card`, `card_roots'`). -/
theorem eq_of_degree_lt_of_forall_iterate_derivative_eval_eq {m : Multiset F} {p q : F[X]}
    (hp : p.degree < m.card) (hq : q.degree < m.card)
    (h : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] p).eval y = (derivative^[k] q).eval y) :
    p = q := by
  sorry

/-- **Hermite interpolation**: over a field of characteristic $0$, for every multiset $m$ of
nodes and all prescribed values $r(y, k)$, there is a polynomial $H$ of degree less than
$\lvert m\rvert$ with $H^{(k)}(y) = r(y, k)$ for every $y \in m$ and every $k$ below the
multiplicity of $y$. [Davis1975, Theorem 2.7.1] (locator to check).
Proof: M, about 45 lines. The jet map from `degreeLT F m.card` (dimension $\lvert m\rvert$,
`Polynomial.degreeLT` with `dim_degreeLT`) to
$\prod_{y \in m.\mathrm{toFinset}}F^{\mathrm{count}\,y}$
(dimension $\sum_y \mathrm{count}\,y = \lvert m\rvert$, `Multiset.toFinset_sum_count_eq`) is
linear and injective by `eq_of_degree_lt_of_forall_iterate_derivative_eval_eq`, hence surjective
(`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`). Alternatively, the Chinese
remainder theorem for the pairwise coprime $(X - y)^{\mathrm{count}\,y}$ and the Taylor
polynomials of the data, reduced modulo $\omega_m$. -/
theorem exists_degree_lt_forall_iterate_derivative_eval_eq (m : Multiset F) (r : F → ℕ → F) :
    ∃ H : F[X], H.degree < m.card ∧
      ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] H).eval y = r y k := by
  sorry

end Algebra

/-! ### The remainder -/

/-- **The Hermite interpolation remainder**: let $a < b$, $m$ a nonempty multiset of points of
$[a, b]$ with every point of multiplicity at least $2$ in $(a, b)$, $f$ continuous on $[a, b]$
and $C^{\lvert m\rvert}$ on $(a, b)$, and $H$ a real polynomial of degree less than
$\lvert m\rvert$ with $H^{(k)}(y) = f^{(k)}(y)$ for every $y \in m$ and every $k$ below the
multiplicity of $y$. Then for every $x \in [a, b]$ there is $\xi \in (a, b)$ with
$$f(x) - H(x) = \frac{f^{(\lvert m\rvert)}(\xi)}{\lvert m\rvert!}\prod_{y\in m}(x - y)\,.$$
[Davis1975, Theorem 3.5.1]; [Gautschi2004, §1.4.2] (locators to check); there for distinct
nodes of multiplicity at most $2$ with $\xi$ in the hull of the nodes and $x$; here any
multiplicities, simple nodes allowed at the endpoints.
Proof: L, about 120 lines; the prototype proves it
(`NLAlib.exists_sub_eval_eq_iteratedDeriv_mul_of_multiset`,
`NLAlib/Polynomial/Quadrature/HermiteRemainder.lean`). If $\omega_m(x) = 0$ then $x \in m$ and
both sides vanish (`hjet` at $k = 0$; take $\xi = (a + b)/2$). Otherwise set
$K = (f(x) - H(x))/\omega_m(x)$ and $g = f - (H + K\omega_m)$: $g$ has the jets of $0$ on $m$
and $g(x) = 0$, so the multiset $m + \{x\}$ of $\lvert m\rvert + 1$ zeros, through
`exists_iteratedDeriv_eq_zero_of_multiset` with $q = \lvert m\rvert - 1$, gives
$g^{(\lvert m\rvert)}(\xi) = 0$. The polynomial part is `Polynomial.iteratedDeriv` (as an
`EqOn` on the open interval; the prototype's `iteratedDeriv_sub_eval_eqOn`), $H^{(\lvert
m\rvert)} = 0$ (`iterate_derivative_eq_zero_of_degree_lt`) and
$\omega_m^{(\lvert m\rvert)} = \lvert m\rvert!$ (`Polynomial.iterate_derivative_natDegree`,
`natDegree_multiset_prod_X_sub_C_eq_card`, `monic_multiset_prod_of_monic`). The jets of
$\omega_m$ vanish on $m$ because $(X - y)^{\mathrm{count}\,y}$ divides it
(`isRoot_iterate_derivative_of_lt_rootMultiplicity`, `count_roots`,
`roots_multiset_prod_X_sub_C`).
Result: hermite-interpolation-remainder -/
theorem exists_sub_eval_eq_iteratedDeriv_mul {a b : ℝ} (hab : a < b) {m : Multiset ℝ}
    (hm : m ≠ 0) (hmem : ∀ y ∈ m, y ∈ Set.Icc a b)
    (hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Set.Ioo a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ m.card f (Set.Ioo a b)) {H : ℝ[X]}
    (hH : H.degree < m.card)
    (hjet : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] H).eval y = iteratedDeriv k f y)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b, f x - H.eval x =
      iteratedDeriv m.card f ξ / m.card.factorial * ((m.map fun y => X - C y).prod).eval x := by
  sorry

/-- **The Lagrange interpolation remainder**: for $a < b$, a nonempty finite set $s$ of nodes
in $[a, b]$, $f$ continuous on $[a, b]$ and $C^{\lvert s\rvert}$ on $(a, b)$, and every
$x \in [a, b]$, there is $\xi \in (a, b)$ with
$$f(x) - p_s(x) = \frac{f^{(\lvert s\rvert)}(\xi)}{\lvert s\rvert!}\prod_{y\in s}(x - y)\,,$$
$p_s$ the Lagrange interpolant of $f$ at $s$ (Mathlib's `Lagrange.interpolate s id f`).
[Davis1975, Theorem 3.1.1]; [Trefethen2019, Ch. 11] (locators to check); there with $\xi$ in
the hull of $s$ and $x$.
Proof: S, about 15 lines. `exists_sub_eval_eq_iteratedDeriv_mul` with $m = s.\mathrm{val}$
(`Finset.card_val`, every count is $1$ by `Multiset.count_eq_one_of_mem` and `s.nodup`, so
`hrep` is vacuous and only $k = 0$ occurs in the jets): `Lagrange.degree_interpolate_lt`,
`Lagrange.eval_interpolate_at_node`, and `Lagrange.nodal` is the multiset product
(`Lagrange.nodal`, `Finset.prod_eq_multiset_prod`).
Result: lagrange-interpolation-remainder -/
theorem exists_sub_eval_interpolate_eq_iteratedDeriv_mul {a b : ℝ} (hab : a < b) {s : Finset ℝ}
    (hs : s.Nonempty) (hsab : (s : Set ℝ) ⊆ Set.Icc a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ s.card f (Set.Ioo a b)) {x : ℝ}
    (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b, f x - (Lagrange.interpolate s id f).eval x =
      iteratedDeriv s.card f ξ / s.card.factorial * (Lagrange.nodal s id).eval x := by
  sorry

end NLAlib
