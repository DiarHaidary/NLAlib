/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Chebyshev.Residual

/-!
# Residual polynomials on two symmetric intervals

On $S = [-a', -a] \cup [a, a']$, $0 < a < a'$, the best residual polynomial of degree at most $q$
($p(0) = 1$) is even, $r_k(x^2)$ with $k = \lfloor q/2 \rfloor$ and $r_k$ the normalized
Chebyshev residual of $[a^2, a'^2]$, so the residual minimax value of $S$ is
$T_k\bigl((a'^2 + a^2)/(a'^2 - a^2)\bigr)^{-1}$. Its dual certificate lives on the $2(k + 1)$
points $\pm\sqrt{\xi_j}$, with $\xi_j$ the Chebyshev extrema of $[a^2, a'^2]$ and half the dual
weights $\omega_j$ on each sign. For $a = 1$, $a' = \kappa \ge 2$ the value is at least
$e^{-2q/\kappa}$: Lemmas 1 and 2 of [Shamir2026], with an explicit certificate in place of the
Kroó–Pinkus characterization.

A **Chebyshev two-interval spectrum** (`IsChebyshevTwoIntervalSpectrum`) is a list of
$\lvert n \rvert$ values on those $2(k + 1)$ points, each taken often enough that the counting
measure dominates $\lvert n \rvert/4$ times the normalized dual weights plus a margin $M$; it is
the spectrum of the hard instance of the linear-system lower bound. The scaffold has the
statements (design note `docs/design/LowerBounds-HiddenRotationLowerBounds.md`).

## Main definitions

* `NLAlib.IsChebyshevTwoIntervalSpectrum`: values on the two-interval Chebyshev points with
  multiplicities dominating the dual weights.
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- A **Chebyshev two-interval spectrum** for $\kappa$, depth $s$ and margin $M$: with
$k = \lfloor s/2 \rfloor$, $\xi_j$ the Chebyshev extrema of $[1, \kappa^2]$ (`chebyshevExtremum`),
$\omega_j$ their dual weights (`chebyshevWeight`) and
$\tau = T_k\bigl((\kappa^2 + 1)/(\kappa^2 - 1)\bigr) = \sum_j \omega_j$, every value $d_i$ is one of
the $2(k + 1)$ points $\pm\sqrt{\xi_j}$, and each point is taken at least
$$\frac{\lvert n \rvert}{4}\cdot\frac{\omega_j}{2\tau} + M$$
times. For $\kappa > 1$ the points lie in $[-\kappa, -1] \cup [1, \kappa]$, and such a spectrum
exists once $4(s + 2)(M + 1) \le 3\lvert n \rvert$ (scaffold). Junk: for $\kappa \le 1$ the
points are not in the two intervals; theorems assume $2 \le \kappa$. -/
structure IsChebyshevTwoIntervalSpectrum {n : Type*} [Fintype n] (κ : ℝ) (s M : ℕ)
    (d : n → ℝ) : Prop where
  /-- Every value is one of the points $\pm\sqrt{\xi_j}$. -/
  exists_eq : ∀ i, ∃ j : Fin (s / 2 + 1),
    d i = Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) ∨
      d i = -Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)
  /-- The point $+\sqrt{\xi_j}$ is taken at least $\lvert n \rvert\omega_j/(8\tau) + M$ times. -/
  le_card_pos : ∀ j : Fin (s / 2 + 1),
    (Fintype.card n : ℝ) / 4 * (chebyshevWeight 1 (κ ^ 2) (s / 2) j /
        (2 * (T ℝ ((s / 2 : ℕ) : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)))) + M ≤
      ((Finset.univ.filter fun i =>
        d i = Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)).card : ℝ)
  /-- The point $-\sqrt{\xi_j}$ is taken at least $\lvert n \rvert\omega_j/(8\tau) + M$ times. -/
  le_card_neg : ∀ j : Fin (s / 2 + 1),
    (Fintype.card n : ℝ) / 4 * (chebyshevWeight 1 (κ ^ 2) (s / 2) j /
        (2 * (T ℝ ((s / 2 : ℕ) : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)))) + M ≤
      ((Finset.univ.filter fun i =>
        d i = -Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)).card : ℝ)

end NLAlib
