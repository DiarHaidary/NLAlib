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

On a finite set $s$ of reals, a sum $\sum_{x\in s} f(x)d(x)$ against an $L$-Lipschitz $f$ is
controlled by the partial sums $\sum_{y\in s,\,y\le x} d(y)$: a finite Abel summation, with no
Stieltjes integral. Upstream candidates for `Mathlib.Topology.MetricSpace.Lipschitz`; Mathlib's
summation by parts (`Finset.sum_range_by_parts`) is over `ℕ` ranges.

Design: `docs/design/Estimation-SLQ.md` §3.1, F1 and F2.

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
$$\Bigl\lvert\sum_{x\in s} f(x)d(x) - f(t)\sum_{x\in s} d(x)\Bigr\rvert \le L(t - a)K\,.$$ -/
theorem abs_sum_mul_sub_mul_sum_le_of_lipschitzOnWith {s : Finset ℝ}
    {a b t : ℝ} (hs : ∀ x ∈ s, x ∈ Set.Icc a t) (hat : a ≤ t) (htb : t ≤ b) {f : ℝ → ℝ}
    {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc a b)) (d : ℝ → ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ s, |∑ y ∈ s with y ≤ x, d y| ≤ K) :
    |∑ x ∈ s, f x * d x - f t * ∑ x ∈ s, d x| ≤ L * (t - a) * K := by
  induction s using Finset.induction_on_max generalizing t with
  | empty =>
    simp only [sum_empty, mul_zero, sub_zero, abs_zero]
    positivity
  | insert x₀ s' hlt ih =>
    have hx₀ : x₀ ∉ s' := fun h => lt_irrefl _ (hlt x₀ h)
    have hx₀t := hs x₀ (mem_insert_self _ _)
    -- below a point of `s'`, the partial sums of `insert x₀ s'` are those of `s'`
    have h1 := ih (t := x₀) (fun x hx => ⟨(hs x (mem_insert_of_mem hx)).1, (hlt x hx).le⟩)
      hx₀t.1 (hx₀t.2.trans htb) fun x hx => by
        have := hK x (mem_insert_of_mem hx)
        rwa [filter_insert, if_neg (hlt x hx).not_ge] at this
    have h2 : |d x₀ + ∑ x ∈ s', d x| ≤ K := by
      have htot := (forall_mem_insert _ _ (· ≤ x₀)).2 ⟨le_rfl, fun x hx => (hlt x hx).le⟩
      have := hK x₀ (mem_insert_self _ _)
      rwa [filter_true_of_mem htot, sum_insert hx₀] at this
    have h3 : |f x₀ - f t| ≤ L * (t - x₀) := by
      have := hf.dist_le_mul x₀ ⟨hx₀t.1, hx₀t.2.trans htb⟩ t ⟨hat, htb⟩
      rwa [Real.dist_eq, Real.dist_eq, abs_sub_comm x₀, abs_of_nonneg (sub_nonneg.mpr hx₀t.2)]
        at this
    have := sub_nonneg.mpr hx₀t.2
    rw [sum_insert hx₀, sum_insert hx₀]
    calc _ = |(∑ x ∈ s', f x * d x - f x₀ * ∑ x ∈ s', d x)
            + (f x₀ - f t) * (d x₀ + ∑ x ∈ s', d x)| := by ring_nf
      _ ≤ L * (x₀ - a) * K + L * (t - x₀) * K := by
        grw [abs_add_le, abs_mul, h1, h3, h2]
      _ = L * (t - a) * K := by ring

/-- Abel summation against a Lipschitz function, absolute form: if every point of the finite set
$s$ lies in $[a, b]$, $a \le b$, $f$ is $L$-Lipschitz on $[a, b]$, $K \ge 0$, and every partial
sum $\sum_{y\in s,\,y\le x} d(y)$ with $x \in s$ is at most $K$ in absolute value, then
$$\Bigl\lvert\sum_{x\in s} f(x)d(x)\Bigr\rvert \le (\lvert f(b)\rvert + L(b - a))K\,.$$
The term $\lvert f(b)\rvert K$ bounds $f(b)$ times the total, the partial sum at the largest
point. -/
theorem abs_sum_mul_le_of_lipschitzOnWith {s : Finset ℝ} {a b : ℝ}
    (hs : ∀ x ∈ s, x ∈ Set.Icc a b) (hab : a ≤ b) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) (d : ℝ → ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ s, |∑ y ∈ s with y ≤ x, d y| ≤ K) :
    |∑ x ∈ s, f x * d x| ≤ (|f b| + L * (b - a)) * K := by
  have := sub_nonneg.mpr hab
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [sum_empty, abs_zero]
    positivity
  have hT : |∑ x ∈ s, d x| ≤ K := by
    have := hK _ (max'_mem s hne)
    rwa [filter_true_of_mem fun y hy => le_max' s y hy] at this
  have htri := abs_sub_abs_le_abs_sub (∑ x ∈ s, f x * d x) (f b * ∑ x ∈ s, d x)
  rw [abs_mul] at htri
  linarith [abs_sum_mul_sub_mul_sum_le_of_lipschitzOnWith hs hab le_rfl hf d hK0 hK,
    mul_le_mul_of_nonneg_left hT (abs_nonneg (f b))]

end Finset
