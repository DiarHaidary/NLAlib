/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Chebyshev growth outside the unit interval

Radical formulas and lower bounds for Mathlib's first-kind Chebyshev polynomials.
These are upstream candidates in `Polynomial.Chebyshev`.

## Main results

* `Polynomial.Chebyshev.eval_T_real_eq_of_one_le`: the radical closed form.
* `Polynomial.Chebyshev.pow_div_two_le_eval_T_real`: exponential lower growth.
* `Polynomial.Chebyshev.sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real`:
  the square-root condition-ratio lower bound.
* `Polynomial.Chebyshev.eval_T_two_mul`: $T_{2j}(x) = T_j(2x^2 - 1)$.
* `Polynomial.Chebyshev.monotoneOn_eval_T_real`: $T_q$ is monotone on $[1, \infty)$.
* `Real.exp_two_mul_le_one_add_div_one_sub`: $e^{2r} \le (1 + r)/(1 - r)$ on $[0, 1)$.
* `Polynomial.Chebyshev.exp_mul_sqrt_div_two_le_eval_T_real`: the gap form of Chebyshev growth,
  $\tfrac12 e^{2q\sqrt{r}} \le T_q((1 + r)/(1 - r))$.
* `Polynomial.Chebyshev.le_exp_of_eval_T_real_le`: an inverse of Chebyshev growth,
  $T_q(x) \le y \Rightarrow x \le \exp((\log(2y)/q)^2/2)$.
-/

@[expose] public section

namespace Polynomial.Chebyshev

open Real

/-- For $x\ge1$, the radical closed form is
$$T_q(x)=\frac{(x+\sqrt{x^2-1})^q+(x-\sqrt{x^2-1})^q}{2}.$$
[Saad2003, §6.11.1, Eq. (6.111)], with the reciprocal term rewritten algebraically.

Result: chebyshev-growth
-/
theorem eval_T_real_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (T ℝ (q : ℤ)).eval x =
      ((x + Real.sqrt (x ^ 2 - 1)) ^ q + (x - Real.sqrt (x ^ 2 - 1)) ^ q) / 2 := by
  have hs : 0 < x + √(x ^ 2 - 1) := by positivity
  have h := T_real_cosh (arcosh x) (q : ℤ)
  rw [cosh_arcosh hx] at h
  rw [h, arcosh, ← add_sqrt_self_sq_sub_one_inv hx, Int.cast_natCast, ← Real.log_pow,
    cosh_log (pow_pos hs q), inv_pow]

/-- For $x\ge1$, the Chebyshev polynomial satisfies
$$(x+\sqrt{x^2-1})^q/2\le T_q(x).$$
[Saad2003, proof of Theorem 6.29, Eqs. (6.124)–(6.128)].
-/
theorem pow_div_two_le_eval_T_real {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (x + Real.sqrt (x ^ 2 - 1)) ^ q / 2 ≤ (T ℝ (q : ℤ)).eval x := by
  rw [eval_T_real_eq_of_one_le hx]
  have hs : 0 ≤ x - √(x ^ 2 - 1) := by
    rw [← add_sqrt_self_sq_sub_one_inv hx]
    positivity
  have := pow_nonneg hs q
  linarith

/-- For $0<a<b$, the condition-ratio form of Chebyshev growth is
$$\frac12\left(\frac{\sqrt b+\sqrt a}{\sqrt b-\sqrt a}\right)^q
\le T_q\left(\frac{b+a}{b-a}\right).$$
[Saad2003, proof of Theorem 6.29, Eqs. (6.124)–(6.128)].
-/
theorem sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (q : ℕ) :
    ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) ^ q / 2 ≤
      (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) := by
  have key : ∀ s t : ℝ, 0 < s → s < t →
      (t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2) +
        √(((t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2)) ^ 2 - 1) = (t + s) / (t - s) := by
    intro s t hs hst
    have hd : 0 < t ^ 2 - s ^ 2 := by nlinarith
    have hts : 0 < t - s := by linarith
    have hsq : ((t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2)) ^ 2 - 1 =
        (2 * t * s / (t ^ 2 - s ^ 2)) ^ 2 := by
      field_simp
      ring
    have ht : 0 < t := by linarith
    rw [hsq, Real.sqrt_sq (div_nonneg (by positivity) hd.le)]
    field_simp
    ring
  have h := key (√a) (√b) (Real.sqrt_pos.2 ha) (Real.sqrt_lt_sqrt ha.le hab)
  rw [Real.sq_sqrt ha.le, Real.sq_sqrt (by linarith)] at h
  rw [← h]
  exact pow_div_two_le_eval_T_real (by rw [le_div_iff₀ (by linarith)]; linarith) q

-- Stage B2a

/-- **Chebyshev composition with $T_2$**: $T_{2j}(x) = T_j(2x^2 - 1)$, for every integer $j$ and
every commutative ring. [TroppWebber2023, Lemma 9.3], part 1 in the form used there. -/
theorem eval_T_two_mul {R : Type*} [CommRing R] (j : ℤ) (x : R) :
    (T R (2 * j)).eval x = (T R j).eval (2 * x ^ 2 - 1) := by
  sorry

/-- **Monotonicity outside the unit interval**: $T_q$ is non-decreasing on $[1, \infty)$.
[TroppWebber2023, Lemma 9.3], part 3. -/
theorem monotoneOn_eval_T_real (q : ℕ) :
    MonotoneOn (fun x : ℝ => (T ℝ (q : ℤ)).eval x) (Set.Ici 1) := by
  sorry

end Polynomial.Chebyshev

namespace Real

/-- $e^{2r} \le \frac{1 + r}{1 - r}$ for $0 \le r < 1$, that is $r \le \operatorname{artanh} r$.
[TroppWebber2023, (C.1)]. -/
theorem exp_two_mul_le_one_add_div_one_sub {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) :
    exp (2 * r) ≤ (1 + r) / (1 - r) := by
  sorry

end Real

namespace Polynomial.Chebyshev

open Real

/-- **Chebyshev growth in terms of a relative gap**: for $0 \le r < 1$,
$$\frac12 e^{2q\sqrt{r}} \le T_q\Bigl(\frac{1 + r}{1 - r}\Bigr)\,.$$
With $r$ a relative gap $\gamma$, $(1 + \gamma)/(1 - \gamma)$ is the ratio of the two singular
values. [TroppWebber2023, Lemma 9.3], part 3. -/
theorem exp_mul_sqrt_div_two_le_eval_T_real (q : ℕ) {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) :
    exp (2 * q * √r) / 2 ≤ (T ℝ (q : ℤ)).eval ((1 + r) / (1 - r)) := by
  sorry

-- Stage B2b

/-- **Inverting Chebyshev growth**: for $q > 0$ and $x \ge 1$, if $T_q(x) \le y$ then
$$x \le \exp\Bigl(\frac{1}{2}\Bigl(\frac{\log(2y)}{q}\Bigr)^2\Bigr)\,.$$
Stated as an implication, with no inverse function: $T_q(x) = \cosh(q\operatorname{arcosh}x)$,
$\operatorname{arcosh} y \le \log(2y)$ and $\cosh t \le e^{t^2/2}$. The hypothesis $1 \le y$ follows
from the others. [TroppWebber2023, Lemma 9.3], part 4. -/
theorem le_exp_of_eval_T_real_le {q : ℕ} (hq : 0 < q) {x y : ℝ} (hx : 1 ≤ x)
    (h : (T ℝ (q : ℤ)).eval x ≤ y) : x ≤ exp ((log (2 * y) / q) ^ 2 / 2) := by
  sorry

end Polynomial.Chebyshev
