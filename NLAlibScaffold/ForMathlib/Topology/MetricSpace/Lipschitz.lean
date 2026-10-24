/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Abel summation against a Lipschitz function

Statements for `NLAlib/ForMathlib/Topology/MetricSpace/Lipschitz.lean` whose proofs are deferred
(`docs/design/Estimation-SLQ.md`, §3.1, F1 and F2). On a finite set $s$ of reals, a sum
$\sum_{x\in s} f(x)d(x)$ against an $L$-Lipschitz $f$ is controlled by the partial sums
$\sum_{y\in s,\,y\le x} d(y)$: a finite Abel summation, with no Stieltjes integral. Upstream
candidates for `Mathlib.Topology.MetricSpace.Lipschitz`; Mathlib's summation by parts
(`Finset.sum_range_by_parts`) is over `ℕ` ranges.

## Main results

* `Finset.abs_sum_mul_sub_mul_sum_le_of_lipschitzOnWith`: the sum minus $f(t)$ times the total.
* `Finset.abs_sum_mul_le_of_lipschitzOnWith`: the sum itself, with the term $\lvert f(b)\rvert$.
-/

@[expose] public section

open scoped NNReal

namespace Finset

/-- Abel summation against a Lipschitz function on a finite set of reals: if every point of the
finite set $s$ lies in $[a, t]$, $a \le t \le b$, $f$ is $L$-Lipschitz on $[a, b]$, $K \ge 0$,
and every partial sum $\sum_{y\in s,\,y\le x} d(y)$ with $x \in s$ is at most $K$ in absolute
value, then
$$\Bigl\lvert\sum_{x\in s} f(x)d(x) - f(t)\sum_{x\in s} d(x)\Bigr\rvert \le L(t - a)K\,.$$
Proof: M, about 55 lines. `Finset.induction_on_max`, generalising `t`: for `insert x₀ s'` with
every point of `s'` below `x₀`, the filters below a point `y < x₀` do not see `x₀`
(`Finset.sum_insert`, `Finset.filter_insert`); the induction hypothesis at `t := x₀`;
`LipschitzOnWith.dist_le_mul`, `Real.dist_eq` for $\lvert f(x_0) - f(t)\rvert \le L(t - x_0)$
times the total, at most $K$; `abs_add`, `mul_le_mul`, `linarith`. -/
theorem abs_sum_mul_sub_mul_sum_le_of_lipschitzOnWith {s : Finset ℝ}
    {a b t : ℝ} (hs : ∀ x ∈ s, x ∈ Set.Icc a t) (hat : a ≤ t) (htb : t ≤ b) {f : ℝ → ℝ}
    {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc a b)) (d : ℝ → ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ s, |∑ y ∈ s with y ≤ x, d y| ≤ K) :
    |∑ x ∈ s, f x * d x - f t * ∑ x ∈ s, d x| ≤ L * (t - a) * K := by
  sorry

/-- Abel summation against a Lipschitz function, absolute form: if every point of the finite set
$s$ lies in $[a, b]$, $a \le b$, $f$ is $L$-Lipschitz on $[a, b]$, $K \ge 0$, and every partial
sum $\sum_{y\in s,\,y\le x} d(y)$ with $x \in s$ is at most $K$ in absolute value, then
$$\Bigl\lvert\sum_{x\in s} f(x)d(x)\Bigr\rvert \le (\lvert f(b)\rvert + L(b - a))K\,.$$
The term $\lvert f(b)\rvert K$ bounds $f(b)$ times the total, the partial sum at the largest point.
Proof: S, about 20 lines. `Finset.abs_sum_mul_sub_mul_sum_le_of_lipschitzOnWith` at `t := b`;
$\lvert\sum_{x\in s} d(x)\rvert \le K$ from `hK` at `s.max'` (`Finset.filter_true_of_mem`,
`Finset.le_max'`), the empty case separately; `abs_sub_abs_le_abs_sub`, `abs_mul`, `linarith`. -/
theorem abs_sum_mul_le_of_lipschitzOnWith {s : Finset ℝ} {a b : ℝ}
    (hs : ∀ x ∈ s, x ∈ Set.Icc a b) (hab : a ≤ b) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) (d : ℝ → ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ s, |∑ y ∈ s with y ≤ x, d y| ≤ K) :
    |∑ x ∈ s, f x * d x| ≤ (|f b| + L * (b - a)) * K := by
  sorry

end Finset
