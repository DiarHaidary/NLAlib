/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.NewtonSchulz
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Convergence of the perturbed scalar Newton–Schulz iteration (scaffold)

Statements for `NLAlib/Polynomial/Approximation/NewtonSchulz.lean` (stage HDIAG, wave W1, design
note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.1): the algebra of
$g(x) = \tfrac12 x(3 - x^2)$, its sign preservation and monotonicity under a perturbation of size
$u$, the quadratic decrease of $\lvert 1 - x^2 \rvert$, and the step count of the perturbed
iteration ([Shah2024, Lemmas 2.3–2.5]).

## Main results

* `NLAlib.one_sub_newtonSchulz_sq`: $1 - g(x)^2 = (1 - x^2)^2(4 - x^2)/4$.
* `NLAlib.mul_newtonSchulz_add_pos`, `NLAlib.abs_le_abs_newtonSchulz_add`: Lemma 2.3.
* `NLAlib.abs_one_sub_sq_newtonSchulz_add_le`,
  `NLAlib.abs_one_sub_sq_newtonSchulz_add_le_add`: Lemma 2.4.
* `NLAlib.abs_one_sub_sq_le_of_newtonSchulzSteps_le`: Lemma 2.5.
-/

@[expose] public section

namespace NLAlib

/-- The Newton–Schulz map is odd: $g(-x) = -g(x)$.
Proof: unfold `NLAlib.newtonSchulz`; `ring`. S, about 2 lines. -/
theorem newtonSchulz_neg (x : ℝ) : newtonSchulz (-x) = -newtonSchulz x := by
  unfold newtonSchulz
  ring

/-- **The defect identity of the Newton–Schulz map**: for every real $x$,
$$1 - g(x)^2 = \frac{(1 - x^2)^2(4 - x^2)}{4} \,.$$
No printed source; it gives both the range of $g$ and its quadratic convergence.
Proof: unfold `NLAlib.newtonSchulz`; `ring`. S, about 2 lines. -/
theorem one_sub_newtonSchulz_sq (x : ℝ) :
    1 - newtonSchulz x ^ 2 = (1 - x ^ 2) ^ 2 * (4 - x ^ 2) / 4 := by
  sorry

/-- The Newton–Schulz map sends $[-2, 2]$ into $[-1, 1]$: $\lvert g(x) \rvert \le 1$ for
$\lvert x \rvert \le 2$. [Shah2024, proof of Lemma 2.5], there on $[-1.5, 1.5]$.
Proof: by `NLAlib.one_sub_newtonSchulz_sq` the defect $1 - g(x)^2$ is a square times
$(4 - x^2)/4 \ge 0$ (`sq_abs`, `abs_le_of_sq_le_sq'` or `abs_le_one_iff_mul_self_le_one`,
`nlinarith`). S, about 8 lines. -/
theorem abs_newtonSchulz_le_one {x : ℝ} (hx : |x| ≤ 2) : |newtonSchulz x| ≤ 1 := by
  sorry

/-- **The perturbed Newton–Schulz step keeps the sign** (Lemma 2.3, first part): if
$\lvert \xi \rvert \le u$ and $u < \lvert x \rvert < \sqrt3 - (\sqrt3 - 1)u$, then $g(x) + \xi$
has the sign of $x$, that is $x(g(x) + \xi) > 0$. [Shah2024, Lemma 2.3], there with
$u \le 3/16$, not needed here.
Proof: by oddness (`NLAlib.newtonSchulz_neg`) reduce to $x > 0$. $g$ is concave on $[0, \sqrt3]$,
so it lies above the chords through $(0,0)$, $(1,1)$, $(\sqrt3, 0)$: $g(x) \ge x$ on $[0,1]$ and
$g(x) \ge (\sqrt3 - x)/(\sqrt3 - 1)$ on $[1, \sqrt3]$ (polynomial inequalities, `nlinarith`
with `Real.sq_sqrt`, `Real.sqrt_lt_sqrt`); both exceed $u \ge \lvert \xi \rvert$ on the range.
M, about 25 lines. -/
theorem mul_newtonSchulz_add_pos {u x ξ : ℝ} (hξ : |ξ| ≤ u) (hux : u < |x|)
    (hx : |x| < √3 - (√3 - 1) * u) : 0 < x * (newtonSchulz x + ξ) := by
  sorry

/-- **The perturbed Newton–Schulz step does not decrease the modulus** (Lemma 2.3, second part):
if $\lvert \xi \rvert \le u$ and $\tfrac83 u \le \lvert x \rvert \le 1 - \tfrac83 u$, then
$\lvert x \rvert \le \lvert g(x) + \xi \rvert$. [Shah2024, Lemma 2.3].
Proof: by oddness reduce to $x \ge 0$. $g(x) - x = (x - x^3)/2 \ge \tfrac38\min(x, 1 - x)$ on
$[0, 1]$ (concavity, chords through $0$, $1/2$, $1$; `nlinarith`), which is at least $u$ on the
range, so $g(x) + \xi \ge g(x) - u \ge x \ge 0$. S, about 20 lines. -/
theorem abs_le_abs_newtonSchulz_add {u x ξ : ℝ} (hξ : |ξ| ≤ u) (h₁ : 8 / 3 * u ≤ |x|)
    (h₂ : |x| ≤ 1 - 8 / 3 * u) : |x| ≤ |newtonSchulz x + ξ| := by
  sorry

/-- **Quadratic decrease of the defect under perturbation** (Lemma 2.4, first part): if
$20\lvert \xi \rvert \le \lvert x \rvert \le 1 - \sqrt{10\lvert \xi \rvert}$, then
$$\lvert 1 - (g(x) + \xi)^2 \rvert \le \lvert 1 - x^2 \rvert^2 \,.$$
[Shah2024, Lemma 2.4].
Proof: by oddness reduce to $0 \le x \le 1$. Either follow the source (for $x \le 1/2$,
$\lvert \xi \rvert \le x/20$; for $x \ge 1/2$, $\lvert \xi \rvert \le (1 - x)^2/10$; in each case
$g(x) - \lvert \xi \rvert \ge \sqrt{2x^2 - x^4}$ by squaring a polynomial inequality, then
$\lvert 1 - y^2 \rvert \le (1 - x^2)^2$ for $y$ between $\sqrt{2x^2 - x^4}$ and $1$), or use
`NLAlib.one_sub_newtonSchulz_sq` and $\lvert (y + \xi)^2 - y^2 \rvert \le
\lvert \xi \rvert(2\lvert y \rvert + \lvert \xi \rvert)$ with $y = g(x)$ and check
$\lvert \xi \rvert(2g(x) + \lvert \xi \rvert) \le (1 - x^2)^2x^2/4$ on both ranges (`nlinarith`
after case split at $1/2$; tight near $x = 1/2$, so keep the exact $g$). M, about 50 lines. -/
theorem abs_one_sub_sq_newtonSchulz_add_le {x ξ : ℝ} (h₁ : 20 * |ξ| ≤ |x|)
    (h₂ : |x| ≤ 1 - √(10 * |ξ|)) : |1 - (newtonSchulz x + ξ) ^ 2| ≤ |1 - x ^ 2| ^ 2 := by
  sorry

/-- **The defect bound with an additive error** (Lemma 2.4, second part): if
$\lvert x \rvert \le \sqrt2$ and $\lvert \xi \rvert \le 1$, then
$$\lvert 1 - (g(x) + \xi)^2 \rvert \le \lvert 1 - x^2 \rvert^2 + 4\lvert \xi \rvert \,.$$
[Shah2024, Lemma 2.4].
Proof: `NLAlib.one_sub_newtonSchulz_sq` gives $\lvert 1 - g(x)^2 \rvert =
(1 - x^2)^2(4 - x^2)/4 \le (1 - x^2)^2$ for $x^2 \le 2$; and
$\lvert (g + \xi)^2 - g^2 \rvert \le \lvert \xi \rvert(2\lvert g \rvert + \lvert \xi \rvert)
\le 3\lvert \xi \rvert$ since $\lvert g(x) \rvert \le 1$ (`NLAlib.abs_newtonSchulz_le_one`);
`abs_sub_abs_le_abs_sub`, `nlinarith`. S, about 15 lines. -/
theorem abs_one_sub_sq_newtonSchulz_add_le_add {x ξ : ℝ} (hx : |x| ≤ √2) (hξ : |ξ| ≤ 1) :
    |1 - (newtonSchulz x + ξ) ^ 2| ≤ |1 - x ^ 2| ^ 2 + 4 * |ξ| := by
  sorry

/-- **The perturbed iteration stays in $[-1 - u, 1 + u]$**: if $\lvert x_0 \rvert \le 3/2$,
$u \le 1/2$ and $\lvert x_{k+1} - g(x_k) \rvert \le u$ for every $k$, then
$\lvert x_{k+1} \rvert \le 1 + u$ for every $k$. [Shah2024, proof of Lemma 2.5].
Proof: induction on $k$ with the invariant $\lvert x_k \rvert \le 3/2$:
`NLAlib.abs_newtonSchulz_le_one` and `abs_sub_abs_le_abs_sub`. S, about 15 lines. -/
theorem abs_le_one_add_of_abs_sub_newtonSchulz_le {u : ℝ} {x : ℕ → ℝ} (hu : u ≤ 1 / 2)
    (hx₀ : |x 0| ≤ 3 / 2) (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) (k : ℕ) :
    |x (k + 1)| ≤ 1 + u := by
  sorry

/-- **The perturbed iteration stays away from zero**: if $20u \le \lvert x_0 \rvert \le 3/2$,
$u \le 1/16$ and $\lvert x_{k+1} - g(x_k) \rvert \le u$ for every $k$, then
$\min(\lvert x_0 \rvert, 1/2) \le \lvert x_k \rvert$ for every $k$. No printed source; [Shah2024,
proof of Theorem 2.6] uses it implicitly when it bounds every step by $a/b$.
Proof: induction with the invariant $\min(\lvert x_0 \rvert, 1/2) \le \lvert x_k \rvert \le 3/2$:
on $[\tfrac83 u, 1 - \tfrac83 u]$ use `NLAlib.abs_le_abs_newtonSchulz_add`; on
$(1 - \tfrac83 u, 3/2]$, $\lvert g(x) \rvert \ge g(3/2) = 9/16$ (monotone pieces of $g$ on
$[5/6, 1]$ and $[1, 3/2]$, `nlinarith`), so $\lvert x_{k+1} \rvert \ge 9/16 - u \ge 1/2$; the upper
bound from `NLAlib.abs_le_one_add_of_abs_sub_newtonSchulz_le`. M, about 40 lines. -/
theorem min_abs_le_abs_of_abs_sub_newtonSchulz_le {u : ℝ} {x : ℕ → ℝ} (hu : u ≤ 1 / 16)
    (h₂₀ : 20 * u ≤ |x 0|) (hx₀ : |x 0| ≤ 3 / 2)
    (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) (k : ℕ) :
    min |x 0| (1 / 2) ≤ |x k| := by
  sorry

/-- **Convergence of the perturbed Newton–Schulz iteration** (Lemma 2.5): if
$0 < \varepsilon \le 3/80$, $10u \le \varepsilon$, $x_0 \ne 0$ with
$20u \le \lvert x_0 \rvert \le 3/2$, and $\lvert x_{k+1} - g(x_k) \rvert \le u$ for every $k$,
then for every natural $N \ge N(x_0, \varepsilon)$ (`NLAlib.newtonSchulzSteps`),
$$\lvert 1 - x_N^2 \rvert \le \varepsilon \,.$$
[Shah2024, Lemma 2.5]; there $x_0 \ne 0$ is implicit in $u > 0$.
Proof: the source's proof. Write $m(x) = \lvert 1 - x^2 \rvert$. (1) Once $m(x_k) \le \varepsilon$
it stays: `NLAlib.abs_one_sub_sq_newtonSchulz_add_le_add` gives
$m(x_{k+1}) \le \varepsilon^2 + 4u \le \varepsilon$ (using
`NLAlib.abs_le_one_add_of_abs_sub_newtonSchulz_le`; if $\lvert x_k \rvert \ge 1$ then
$m(x_k) \le 2u + u^2 \le \varepsilon$). (2) Let $S = [20u, 1 - \sqrt\varepsilon]$ and $M$ the
first $k \ge 1$ with $\lvert x_k \rvert \notin S$; while in $S$ the moduli increase
(`NLAlib.abs_le_abs_newtonSchulz_add`) and $m$ squares (`NLAlib.abs_one_sub_sq_newtonSchulz_add_le`,
valid since $1 - \sqrt\varepsilon \le 1 - \sqrt{10u}$), so
$\sqrt\varepsilon \le m(x_{M-1}) \le (1 - x_1^2)^{2^{M-2}}$; with $\log_2(1 - y) \le -y/\log 2$
this gives $M \le \log_2(2\log 2) + 2\log_2(1/\lvert x_1 \rvert) + \log_2\log_2(1/\varepsilon)$,
and $\lvert x_1 \rvert \ge \min(\lvert x_0 \rvert, 1/2)$. (3) Two more steps from
$m(x_M) \le 2\sqrt\varepsilon$ reach $m \le \varepsilon$ ($4.4^2\varepsilon^2 + 0.4\varepsilon \le
\varepsilon$ for $\varepsilon \le 3/80$). Split into private lemmas for (1), (2) and the
logarithm arithmetic (`Real.logb_le_logb`, `Real.log_le_sub_one_of_pos`, `Real.rpow_natCast`).
L, about 150 lines. -/
theorem abs_one_sub_sq_le_of_newtonSchulzSteps_le {u ε : ℝ} {x : ℕ → ℝ} (hε : 0 < ε)
    (hε₁ : 10 * u ≤ ε) (hε₂ : ε ≤ 3 / 80) (h₀ : 0 < |x 0|) (h₂₀ : 20 * u ≤ |x 0|)
    (hx₀ : |x 0| ≤ 3 / 2) (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) {N : ℕ}
    (hN : newtonSchulzSteps (x 0) ε ≤ N) : |1 - x N ^ 2| ≤ ε := by
  sorry

/-- The step count decreases in the starting modulus: for $0 < a \le \lvert x_0 \rvert$,
$N(x_0, \varepsilon) \le N(a, \varepsilon)$.
Proof: unfold `NLAlib.newtonSchulzSteps`; $\min(\lvert x_0 \rvert, 1/2) \ge \min(a, 1/2) > 0$,
`inv_anti₀`, `Real.logb_le_logb_of_le`. S, about 8 lines. -/
theorem newtonSchulzSteps_le_of_le_abs {a x₀ ε : ℝ} (ha : 0 < a) (h : a ≤ |x₀|) :
    newtonSchulzSteps x₀ ε ≤ newtonSchulzSteps a ε := by
  sorry

/-- The step count decreases in the tolerance: for $0 < \varepsilon' \le \varepsilon \le 1/2$,
$N(x_0, \varepsilon) \le N(x_0, \varepsilon')$.
Proof: unfold `NLAlib.newtonSchulzSteps`; $\log_2(1/\varepsilon) \ge 1 > 0$, so both logarithms
are monotone (`Real.logb_le_logb_of_le`, `Real.one_le_logb_iff` or direct). S, about 10 lines. -/
theorem newtonSchulzSteps_le_of_le {x₀ ε ε' : ℝ} (hε' : 0 < ε') (h : ε' ≤ ε) (hε : ε ≤ 1 / 2) :
    newtonSchulzSteps x₀ ε ≤ newtonSchulzSteps x₀ ε' := by
  sorry

end NLAlib
