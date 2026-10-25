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
  induction s using Finset.induction_on_max generalizing t with
  | empty => simp only [sum_empty, mul_zero, sub_zero, abs_zero]; positivity
  | insert x₀ s' hlt ih =>
    have hx₀ : x₀ ∉ s' := fun h => lt_irrefl _ (hlt x₀ h)
    have hx₀t := hs x₀ (mem_insert_self _ _)
    -- partial sums of `s'` below a point of `s'` are those of `insert x₀ s'`
    have hfilt : ∀ x ∈ s', (insert x₀ s').filter (· ≤ x) = s'.filter (· ≤ x) := fun x hx => by
      rw [filter_insert, if_neg (not_le.mpr (hlt x hx))]
    have h1 := ih (t := x₀) (fun x hx => ⟨(hs x (mem_insert_of_mem hx)).1, (hlt x hx).le⟩)
      hx₀t.1 (hx₀t.2.trans htb) fun x hx => by rw [← hfilt x hx]; exact hK x (mem_insert_of_mem hx)
    have htot : (insert x₀ s').filter (· ≤ x₀) = insert x₀ s' :=
      filter_true_of_mem fun x hx => by
        rcases mem_insert.mp hx with rfl | hx
        · exact le_rfl
        · exact (hlt x hx).le
    have h2 : |d x₀ + ∑ x ∈ s', d x| ≤ K := by
      have := hK x₀ (mem_insert_self _ _)
      rwa [htot, sum_insert hx₀] at this
    have h3 : |f x₀ - f t| ≤ L * (t - x₀) := by
      have := hf.dist_le_mul x₀ ⟨hx₀t.1, hx₀t.2.trans htb⟩ t ⟨hat, htb⟩
      rwa [Real.dist_eq, Real.dist_eq, abs_sub_comm x₀, abs_of_nonneg (sub_nonneg.mpr hx₀t.2)]
        at this
    rw [sum_insert hx₀, sum_insert hx₀]
    have heq : f x₀ * d x₀ + ∑ x ∈ s', f x * d x - f t * (d x₀ + ∑ x ∈ s', d x) =
        (∑ x ∈ s', f x * d x - f x₀ * ∑ x ∈ s', d x) + (f x₀ - f t) * (d x₀ + ∑ x ∈ s', d x) := by
      ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h4 := mul_le_mul h3 h2 (abs_nonneg _) (by have := sub_nonneg.mpr hx₀t.2; positivity)
    nlinarith

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
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty, abs_zero]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hL : (0 : ℝ) ≤ L := L.2
    have hfb : 0 ≤ |f b| := abs_nonneg _
    have : 0 ≤ L * (b - a) := mul_nonneg hL hba
    have : 0 ≤ (|f b| + L * (b - a)) := by linarith
    exact mul_nonneg this hK0
  · have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
    have hmem : s.max' hne ∈ s := Finset.max'_mem s hne
    have hT : |∑ x ∈ s, d x| ≤ K := by
      have hfilt : s.filter (fun y => y ≤ s.max' hne) = s :=
        Finset.filter_true_of_mem fun y hy => Finset.le_max' s y hy
      have := hK _ hmem
      rwa [hfilt] at this
    have hmain := abs_sum_mul_sub_mul_sum_le_of_lipschitzOnWith
      (t := b) (fun x hx => hs x hx) hab le_rfl hf d hK0 hK
    have hbnd : |f b * ∑ x ∈ s, d x| ≤ |f b| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hT (abs_nonneg _)
    have htri := abs_sub_abs_le_abs_sub (∑ x ∈ s, f x * d x) (f b * ∑ x ∈ s, d x)
    have hLK : 0 ≤ L * (b - a) * K := by
      have := L.2
      have : 0 ≤ b - a := sub_nonneg.mpr hab
      positivity
    have hrhs : (|f b| + L * (b - a)) * K = |f b| * K + L * (b - a) * K := by ring
    rw [hrhs]
    linarith [abs_sub_comm (f b * ∑ x ∈ s, d x) (∑ x ∈ s, f x * d x)]

end Finset
