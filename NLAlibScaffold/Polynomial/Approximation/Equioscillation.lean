/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Polynomial.Approximation.Equioscillation
public import NLAlibScaffold.Polynomial.Approximation.MinimaxError
public import NLAlibScaffold.ForMathlib.Topology.Order.IntermediateValue
public import NLAlibScaffold.ForMathlib.Topology.ContinuousMap.Compact

/-!
# Equioscillation: the theorems of stage Poly-Best

Statements for `NLAlib/Polynomial/Approximation/Equioscillation.lean` whose proofs are deferred
(`docs/design/Polynomial-BestApproximation.md`, §3.3). De la Vallée Poussin: an error
$f - p$, $\deg p \le n$, that alternates at $n + 2$ points of $s$ with level $\varepsilon$ gives
$\varepsilon \le E_n(f; s)$, on any set and for any $f$. Chebyshev: on $[a, b]$, $a < b$, with
$f$ continuous, $p$ is a best approximation if and only if $f - p$ equioscillates at $n + 2$
points; the best approximation is unique and interpolates $f$ at $n + 1$ interior points. The
Chebyshev polynomial $T_n$ alternates at $n + 1$ points, which gives
$E_n(x^{n + 1}; [-1, 1]) = 2^{-n}$.

## Main results

* `NLAlib.AlternatesOn.mono`, `NLAlib.AlternatesOn.exists_eq_of_abs_le`: the API of the
  predicate.
* `NLAlib.AlternatesOn.exists_le_abs_sub_eval`, `NLAlib.AlternatesOn.le_minimaxError`: de la
  Vallée Poussin's lower bound.
* `NLAlib.AlternatesOn.minimaxError_eq`: an equioscillating error is the minimax error.
* `NLAlib.alternatesOn_of_isUniformApproxOn_minimaxError`,
  `NLAlib.isUniformApproxOn_minimaxError_iff_exists_alternatesOn`: Chebyshev's equioscillation
  theorem.
* `NLAlib.eq_of_isUniformApproxOn_minimaxError`: uniqueness.
* `NLAlib.exists_eval_eq_of_isUniformApproxOn_minimaxError`: the best approximation interpolates.
* `NLAlib.alternatesOn_eval_T_real`, `NLAlib.minimaxError_pow_Icc_neg_one_one`: the Chebyshev
  example.
-/

@[expose] public section

open Polynomial

namespace NLAlib

/-! ### The predicate -/

/-- Alternation is monotone: if $g$ alternates on $s$ at $k$ points with level $\varepsilon$,
then it alternates on every $t \supseteq s$ with every level $\eta \le \varepsilon$.
Proof: S, about 4 lines. The same points and sign; `le_trans`. -/
theorem AlternatesOn.mono {g : ℝ → ℝ} {s t : Set ℝ} {k : ℕ} {ε η : ℝ}
    (h : AlternatesOn g s k ε) (hst : s ⊆ t) (hηε : η ≤ ε) : AlternatesOn g t k η := by
  sorry

/-- An alternation at the level of the uniform bound is an equioscillation: if $g$ alternates on
$s$ at $k$ points with level $\varepsilon$ and $\lvert g \rvert \le \varepsilon$ on $s$, then
there are $x_0 < \dots < x_{k-1}$ in $s$ and $\sigma \in \{1, -1\}$ with
$g(x_i) = \sigma(-1)^i\varepsilon$.
Proof: S, about 10 lines. The same points and sign: $\varepsilon \le \sigma(-1)^ig(x_i) \le
\lvert g(x_i) \rvert \le \varepsilon$ (`le_abs_self`, `abs_mul`, $\lvert\sigma(-1)^i\rvert = 1$),
so $\sigma(-1)^ig(x_i) = \varepsilon$; multiply by $\sigma(-1)^i$ (its square is $1$). -/
theorem AlternatesOn.exists_eq_of_abs_le {g : ℝ → ℝ} {s : Set ℝ} {k : ℕ} {ε : ℝ}
    (h : AlternatesOn g s k ε) (hg : ∀ x ∈ s, |g x| ≤ ε) :
    ∃ x : Fin k → ℝ, StrictMono x ∧ (∀ i, x i ∈ s) ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ i : Fin k, g (x i) = σ * (-1) ^ (i : ℕ) * ε := by
  sorry

/-! ### De la Vallée Poussin -/

/-- **De la Vallée Poussin's theorem, pointwise.** If $\deg p \le n$ and $f - p$ alternates on
$s$ at $n + 2$ points with level $\varepsilon$, then every real polynomial $q$ of degree at most
$n$ has $\varepsilon \le \lvert f(x) - q(x) \rvert$ at some $x \in s$. No continuity of $f$ and
no structure of $s$ are needed. [Rivlin1981, Ch. 1]; [Trefethen2019, Ch. 10] (locators to check).
Proof: M, about 30 lines. Suppose $\lvert f - q \rvert < \varepsilon$ at all $n + 2$ points
$x_i$ (so $\varepsilon > 0$). Then $\sigma(-1)^i(q - p)(x_i) = \sigma(-1)^i(f - p)(x_i) -
\sigma(-1)^i(f - q)(x_i) > 0$, so the polynomial $q - p$ changes sign between consecutive points;
`exists_strictMono_eq_zero_of_mul_neg` gives $n + 1$ distinct zeros, and
`Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero` (degree at most $n$, `degree_sub_le`)
makes $q = p$, contradicting $\lvert f - p \rvert \ge \varepsilon > \lvert f - q \rvert$ at $x_0$.
Prototype: `NLAlib.exists_abs_sub_eval_ge_of_alternation`
(`Polynomial/BestApproximation/AlternationLowerBound`). -/
theorem AlternatesOn.exists_le_abs_sub_eval {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]} {ε : ℝ}
    (h : AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε) (hp : p.degree ≤ n) {q : ℝ[X]}
    (hq : q.degree ≤ n) : ∃ x ∈ s, ε ≤ |f x - q.eval x| := by
  sorry

/-- **De la Vallée Poussin's lower bound.** If $\deg p \le n$, $p$ is within some finite
$\eta$ of $f$ on $s$, and $f - p$ alternates on $s$ at $n + 2$ points with level
$\varepsilon$, then $\varepsilon \le E_n(f; s)$. The set $s$ is arbitrary (a finite spectrum, a
union of intervals); the finite $\eta$ only excludes the junk value of `minimaxError`.
[Rivlin1981, Ch. 1]; [Trefethen2019, Ch. 10] (locators to check).
Proof: S, about 10 lines. The set defining $E_n$ is nonempty ($\eta$, `hη`); every element
$\varepsilon'$, witnessed by $q$, satisfies $\varepsilon \le \lvert f(x) - q(x) \rvert \le
\varepsilon'$ at the point of `AlternatesOn.exists_le_abs_sub_eval`; `le_csInf`. Prototype:
`NLAlib.le_minimaxError_of_alternation`.
Result: de-la-vallee-poussin -/
theorem AlternatesOn.le_minimaxError {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]} {ε : ℝ}
    (h : AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε) (hp : p.degree ≤ n) {η : ℝ}
    (hη : Metric.IsUniformApproxOn (fun x => p.eval x) f s η) : ε ≤ minimaxError f s n := by
  sorry

/-- **An equioscillating error is the minimax error**: if $\deg p \le n$,
$\lvert f - p \rvert \le \varepsilon$ on $s$ and $f - p$ alternates on $s$ at $n + 2$ points
with level $\varepsilon$, then $E_n(f; s) = \varepsilon$, and $p$ is a best approximation. On
any set, for any $f$: the certificate direction of the equioscillation theorem.
[Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1] (locators to check).
Proof: S, about 6 lines. `AlternatesOn.le_minimaxError` with $\eta = \varepsilon$, and
`minimaxError_le_of_isUniformApproxOn` with $0 \le \varepsilon$ (`Metric.IsUniformApproxOn.nonneg`,
$s$ nonempty from `h`). Prototype: `NLAlib.norm_sub_eq_minimaxError_of_equioscillation`
(`Polynomial/BestApproximation/EquioscillationCertificate`).
Result: equioscillation -/
theorem AlternatesOn.minimaxError_eq {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]} {ε : ℝ}
    (h : AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε) (hp : p.degree ≤ n)
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f s ε) : minimaxError f s n = ε := by
  sorry

/-! ### Chebyshev's equioscillation theorem -/

/-- The sign-block induction behind the equioscillation theorem. Let $e$ be continuous on
$[a, b]$, $E > 0$ and $\lvert e(a) \rvert = E$. Either some real $q$ of degree at most $n$ has
$e(x)q(x) > 0$ at every $x \in [a, b]$ with $\lvert e(x) \rvert = E$, and $e(a)q(x) > 0$ for every
$x \le a$; or $e$ alternates at $n + 2$ points of $\{x \in [a, b] : \lvert e(x) \rvert = E\}$
with level $E$.
Proof: L, about 120 lines, by induction on $n$ generalising $a$. If $e$ never takes $-e(a)$ at
an extremal point of $[a, b]$, the constant $q = e(a)$ works. Otherwise let $y$ be the least
point of $[a, b]$ with $e(y) = -e(a)$ (compact level set, `IsCompact.exists_isLeast`), $u$ the
greatest point of $[a, y]$ with $e(u) = e(a)$ (`IsCompact.exists_isGreatest`) and
$z = (u + y)/2$; every extremal point below $y$ has value $e(a)$ and lies in $[a, u]$. Apply the
hypothesis at $y$ (degree $n - 1$, `Nat` induction): its polynomial $q'$ gives
$q = (X - z)q'$ (degree by `degree_mul_le`, signs by `nlinarith` on the two sides of $z$); its
alternation, preceded by $y$ or $a$ (whichever has the opposite sign to the first point), gives
the $n + 2$ points (`Fin.cons`, `Fin.strictMono_cons`). The base case $n = 0$ is the same split
with $q$ constant and the pair $(a, y)$. Prototype:
`NLAlib.exists_polynomial_extremal_sign_or_alternation`
(`Polynomial/BestApproximation/ExtremalSigns`, 150 lines, proved). -/
private theorem exists_degree_le_or_alternatesOn (n : ℕ) {e : ℝ → ℝ} {a b E : ℝ}
    (he : ContinuousOn e (Set.Icc a b)) (hE : 0 < E) (hab : a ≤ b) (hea : |e a| = E) :
    (∃ q : ℝ[X], q.degree ≤ n ∧ (∀ x ∈ Set.Icc a b, |e x| = E → 0 < e x * q.eval x) ∧
      ∀ x ≤ a, 0 < e a * q.eval x) ∨
    AlternatesOn e {x | x ∈ Set.Icc a b ∧ |e x| = E} (n + 2) E := by
  sorry

/-- **Chebyshev's equioscillation theorem, necessity.** Let $a < b$, $f$ continuous on
$[a, b]$, and $p$ a real polynomial of degree at most $n$ with
$\lvert f - p \rvert \le E_n(f; [a, b])$ on $[a, b]$ (a best approximation). Then $f - p$
alternates on $[a, b]$ at $n + 2$ points with level $E_n(f; [a, b])$: it equioscillates
(`AlternatesOn.exists_eq_of_abs_le`). [Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1]
(locators to check).
Proof: L, about 70 lines. If $E_n = 0$, any $n + 2$ equispaced points of $[a, b]$ with
$\sigma = 1$ (the error vanishes). If $E = E_n > 0$, let $e = f - p$ and $c$ the least point of
$[a, b]$ with $\lvert e(c) \rvert = E$ (it exists: otherwise $\lvert e \rvert < E$ everywhere and
compactness gives a smaller uniform bound, contradicting `minimaxError_le_of_isUniformApproxOn`;
use `IsCompact.exists_isMaxOn`). Apply `exists_degree_le_or_alternatesOn` at $c$: the
alternation is the conclusion (`AlternatesOn.mono`); a sign-matching $q$ makes
`ContinuousMap.exists_pos_norm_sub_smul_lt` (on `C(Set.Icc a b, ℝ)`, $e$ restricted) give
$t > 0$ with $\lvert f - (p + tq) \rvert < E$ uniformly, contradicting
`minimaxError_le_of_isUniformApproxOn`. Prototype:
`NLAlib.exists_alternating_extrema_of_norm_sub_eq_minimaxError`
(`Polynomial/BestApproximation/Equioscillation`, proved).
Result: equioscillation -/
theorem alternatesOn_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) :
    AlternatesOn (fun x => f x - p.eval x) (Set.Icc a b) (n + 2)
      (minimaxError f (Set.Icc a b) n) := by
  sorry

/-- **Chebyshev's equioscillation theorem.** Let $a < b$, $f$ continuous on $[a, b]$ and $p$ a
real polynomial of degree at most $n$. Then $p$ is a best approximation,
$\lvert f - p \rvert \le E_n(f; [a, b])$ on $[a, b]$, if and only if for some $\varepsilon$,
$\lvert f - p \rvert \le \varepsilon$ on $[a, b]$ and $f - p$ alternates at $n + 2$ points of
$[a, b]$ with level $\varepsilon$ (and then $\varepsilon = E_n(f; [a, b])$).
[Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1] (locators to check).
Proof: S, about 8 lines. Forward: `alternatesOn_of_isUniformApproxOn_minimaxError` with
$\varepsilon = E_n$. Backward: `AlternatesOn.minimaxError_eq` rewrites $E_n = \varepsilon$.
Result: equioscillation -/
theorem isUniformApproxOn_minimaxError_iff_exists_alternatesOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) :
    Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
        (minimaxError f (Set.Icc a b) n) ↔
      ∃ ε : ℝ, Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε ∧
        AlternatesOn (fun x => f x - p.eval x) (Set.Icc a b) (n + 2) ε := by
  sorry

/-- **The best approximation is unique**: for $a < b$ and $f$ continuous on $[a, b]$, two real
polynomials $p, q$ of degree at most $n$ that are both within $E_n(f; [a, b])$ of $f$ on
$[a, b]$ are equal. [Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1] (locators to check).
Proof: M, about 40 lines. The midpoint $r = (p + q)/2$ is also best (triangle inequality,
`minimaxError_le_of_isUniformApproxOn` both ways). By
`alternatesOn_of_isUniformApproxOn_minimaxError` and `AlternatesOn.exists_eq_of_abs_le`,
$\lvert f - r \rvert = E_n$ at $n + 2$ points; there
$\lvert f - p \rvert, \lvert f - q \rvert \le E_n$ and $2(f - r) = (f - p) + (f - q)$ force
$p = q$ (`abs_le`, `nlinarith`); `Polynomial.eq_of_degree_sub_lt_of_eval_index_eq` with $n + 2$
distinct nodes. Prototype: `NLAlib.eq_of_norm_sub_eq_minimaxError`
(`Polynomial/BestApproximation/Equioscillation`, proved).
Result: best-approximation-uniqueness -/
theorem eq_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p q : ℝ[X]} (hp : p.degree ≤ n)
    (hq : q.degree ≤ n)
    (hpb : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n))
    (hqb : Metric.IsUniformApproxOn (fun x => q.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) : p = q := by
  sorry

/-- **The best approximation interpolates**: for $a < b$, $f$ continuous on $[a, b]$ and $p$ a
best approximation of degree at most $n$, there are $n + 1$ distinct points of $(a, b)$ at which
$p = f$; $p$ is the Lagrange interpolant of $f$ there (`Lagrange.eq_interpolate_of_eval_eq`).
[Trefethen2019, Ch. 10] (locator to check); there on $[-1, 1]$.
Proof: M, about 40 lines. If $E_n > 0$, `alternatesOn_of_isUniformApproxOn_minimaxError`
gives $n + 2$ points where $f - p$ changes sign, and `exists_strictMono_eq_zero_of_mul_neg`
gives $n + 1$ ordered zeros strictly inside, hence in $(a, b)$; take their image `Finset`
(`Finset.card_image_of_injective`). If $E_n = 0$, $f = p$ on $[a, b]$ and any $n + 1$
equispaced interior points work. Prototype:
`NLAlib.exists_interpolate_eq_of_norm_sub_eq_minimaxError`
(`Polynomial/BestApproximation/BestInterpolant`, proved).
Result: best-approximant-interpolates -/
theorem exists_eval_eq_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) :
    ∃ t : Finset ℝ, t.card = n + 1 ∧ (t : Set ℝ) ⊆ Set.Ioo a b ∧ ∀ x ∈ t, p.eval x = f x := by
  sorry

/-! ### The Chebyshev example -/

/-- **$T_n$ alternates at $n + 1$ points**: the Chebyshev polynomial $T_n$ alternates on
$[-1, 1]$ at $n + 1$ points with level $1$, at the extrema $\cos(j\pi/n)$ in increasing order.
[Trefethen2019, Ch. 3].
Proof: S, about 15 lines. The points $x_i = $ `Polynomial.Chebyshev.node n (n - i)`, increasing by
Mathlib's `strictAntiOn_node`; `eval_T_real_node` gives $T_n(x_i) = (-1)^{n - i}$, so
$\sigma = (-1)^n$ (`pow_sub`, or parity cases); `node_mem_Icc`. The case $n = 0$ ($T_0 = 1$,
one point) is covered by the same formula. -/
theorem alternatesOn_eval_T_real (n : ℕ) :
    AlternatesOn (fun x => (Chebyshev.T ℝ (n : ℤ)).eval x) (Set.Icc (-1) 1) (n + 1) 1 := by
  sorry

/-- **The minimax error of $x^{n + 1}$**: on $[-1, 1]$, the best approximation of $x^{n + 1}$ by
polynomials of degree at most $n$ has error $E_n(x^{n + 1}; [-1, 1]) = 2^{-n}$, attained by
$x^{n + 1} - 2^{-n}T_{n + 1}$; equivalently, $2^{-n}T_{n + 1}$ is the monic polynomial of degree
$n + 1$ of least uniform norm on $[-1, 1]$. [GolubMeurant2010, §2.5.1, Theorem 2.15];
[Trefethen2019, Ch. 10].
Proof: S, about 20 lines. `AlternatesOn.minimaxError_eq` with $p = X^{n + 1} - 2^{-n}T_{n + 1}$,
of degree at most $n$ (`leadingCoeff_T`, `natDegree_T`, `degree_sub_lt`), error
$2^{-n}T_{n + 1}$, bounded by $2^{-n}$ (`abs_eval_T_real_le_one`) and alternating by
`alternatesOn_eval_T_real` scaled by $2^{-n} > 0$. Alternatively from
`Polynomial.Chebyshev.isLeast_chebyshev_monic_minimax`.
Result: chebyshev-monic-minimal -/
theorem minimaxError_pow_Icc_neg_one_one (n : ℕ) :
    minimaxError (fun x => x ^ (n + 1)) (Set.Icc (-1) 1) n = ((2 : ℝ) ^ n)⁻¹ := by
  sorry

end NLAlib
