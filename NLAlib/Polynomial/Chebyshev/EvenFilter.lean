/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# The even Chebyshev filter

The even second-kind Chebyshev filter $b_k(x) = U_{2k}(\sqrt{x})/(2k + 1)$ is a polynomial of
degree $k$ in $x$ (only even powers occur in $U_{2k}$), equal to $1$ at $x = 1$ and bounded by
$1$ in absolute value on $[0, 1]$. On $[0, 1]$ it satisfies
$(1 - x)\,b_k(x)^2 \le (2k + 1)^{-2}$: it suppresses every point away from $1$ at the rate
$1/k$, with no gap.

A power of the filter, with the number of factors chosen from the weight of $\{1\}$, gives the
gap-free polynomial filter step of Kuczyński and Woźniakowski: for a finite measure $\nu$ on
$[0, 1]$ with an atom at $1$ and every $q \ge 1$ there is a polynomial $p$ of degree at most $q$
with $p(1) = 1$ and
$$1 - \frac{\int x\,p(x)^2\,d\nu}{\int p(x)^2\,d\nu} \le
\frac{4}{q^2}\Bigl(1 + \frac{\log(\nu(\mathbb{R})/\nu(\{1\}))}{\log 2}\Bigr)^2\,.$$
Applied to the spectral measure of a positive semidefinite matrix, rescaled to $[0, 1]$, it is
the deterministic step of the random-start Lanczos bound.

## Main definitions

* `NLAlib.evenChebyshevFilter`: $b_k$.

## Main results

* `NLAlib.one_sub_mul_eval_evenChebyshevFilter_sq_le`: the gap-free suppression.
* `NLAlib.exists_natDegree_le_one_sub_integral_mul_div_le`: the filter step for a measure.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- The **even Chebyshev filter** $b_k(x) = U_{2k}(\sqrt{x})/(2k + 1)$, a polynomial of degree
$k$ in $x$: the contraction of the even polynomial $U_{2k}$ (Mathlib's
`Polynomial.Chebyshev.U`), scaled so that $b_k(1) = 1$. -/
noncomputable def evenChebyshevFilter (k : ℕ) : ℝ[X] :=
  C ((2 * k + 1 : ℝ)⁻¹) * contract 2 (Chebyshev.U ℝ ((2 * k : ℕ) : ℤ))

/-- The even Chebyshev filter has degree at most $k$. -/
theorem natDegree_evenChebyshevFilter_le (k : ℕ) : (evenChebyshevFilter k).natDegree ≤ k := by
  sorry

/-- The characterising evaluation: for $x \ge 0$,
$b_k(x) = U_{2k}(\sqrt{x})/(2k + 1)$. -/
theorem eval_evenChebyshevFilter (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (evenChebyshevFilter k).eval x =
      (Chebyshev.U ℝ ((2 * k : ℕ) : ℤ)).eval (√x) / (2 * k + 1) := by
  sorry

/-- The even Chebyshev filter is normalised at $1$: $b_k(1) = 1$. -/
theorem eval_evenChebyshevFilter_one (k : ℕ) : (evenChebyshevFilter k).eval 1 = 1 := by
  sorry

/-- The even Chebyshev filter is bounded by $1$ on $[0, 1]$: $\lvert b_k(x)\rvert \le 1$. -/
theorem abs_eval_evenChebyshevFilter_le_one (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(evenChebyshevFilter k).eval x| ≤ 1 := by
  sorry

/-- Gap-free suppression by the even Chebyshev filter: for $x \in [0, 1]$,
$$(1 - x)\,b_k(x)^2 \le \frac{1}{(2k + 1)^2}\,,$$
from $(1 - y^2)\,U_{2k}(y)^2 \le 1$ on $[-1, 1]$. -/
theorem one_sub_mul_eval_evenChebyshevFilter_sq_le (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (1 - x) * (evenChebyshevFilter k).eval x ^ 2 ≤ 1 / (2 * k + 1) ^ 2 := by
  sorry

/-- **The gap-free polynomial filter step**: for a finite measure $\nu$ supported in
$[0, 1]$ with an atom at $1$, $\nu(\{1\}) > 0$, and every $q \ge 1$, there is a real polynomial
$p$ of degree at most $q$ with $p(1) = 1$ and
$$1 - \frac{\int x\,p(x)^2\,d\nu}{\int p(x)^2\,d\nu} \le
\frac{4}{q^2}\Bigl(1 + \frac{\log(\nu(\mathbb{R})/\nu(\{1\}))}{\log 2}\Bigr)^2\,;$$
$p$ is a power of the even Chebyshev filter, the number of factors chosen from the logarithmic
ratio. [KuczynskiWozniakowski1992, Theorem 4.2] (locator from the quarry, to check); there for
the Lanczos method with a random start, here for any such measure. -/
theorem exists_natDegree_le_one_sub_integral_mul_div_le {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) (h1 : 0 < ν.real {1}) {q : ℕ} (hq : 1 ≤ q) :
    ∃ p : ℝ[X], p.natDegree ≤ q ∧ p.eval 1 = 1 ∧
      1 - (∫ x, x * p.eval x ^ 2 ∂ν) / (∫ x, p.eval x ^ 2 ∂ν) ≤
        4 * (1 + Real.log (ν.real Set.univ / ν.real {1}) / Real.log 2) ^ 2 / q ^ 2 := by
  sorry

end NLAlib
