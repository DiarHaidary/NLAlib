/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import NLAlib.ForMathlib.Topology.MetricSpace.Lipschitz

/-!
# Integrals against finitely supported measures

A finite measure on $\mathbb{R}$ carried by a finite set $s$ integrates every function as a
finite sum over $s$, and its distribution function is a partial sum of its atoms. Two such
measures whose distribution functions are uniformly close on $s$ give close integrals of every
Lipschitz function: the one-dimensional Kantorovich–Rubinstein inequality, weakened to the sup
norm, for finite support. Upstream candidates for
`Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`, beside `setIntegral_finset`.

Design: stage SLQ (`docs/design/Estimation-SLQ.md` §3.1, F3 to F5).

## Main results

* `MeasureTheory.integral_eq_sum_measureReal_singleton_mul`: the integral as a finite sum.
* `MeasureTheory.measureReal_Iic_eq_sum`: the distribution function as a partial sum.
* `MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith`: distribution functions control
  Lipschitz test functions.
-/

@[expose] public section

open scoped NNReal

namespace MeasureTheory

/-- The integral against a finite measure carried by a finite set: if the finite measure $\mu$ on
$\mathbb{R}$ is carried by the finite set $s$, then for every $f : \mathbb{R} \to \mathbb{R}$,
$\int f\,d\mu = \sum_{x\in s}\mu(\{x\})f(x)$; no integrability or measurability of $f$ is needed. -/
theorem integral_eq_sum_measureReal_singleton_mul {μ : Measure ℝ}
    [IsFiniteMeasure μ] {s : Finset ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ s) (f : ℝ → ℝ) :
    ∫ x, f x ∂μ = ∑ x ∈ s, μ.real {x} * f x := by
  have hr : μ.restrict (s : Set ℝ) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by simpa using hμ)
  conv_lhs => rw [← hr]
  rw [setIntegral_finset s IntegrableOn.finset]
  simp only [smul_eq_mul]

/-- The distribution function of a finite measure carried by a finite set: if the finite measure
$\mu$ on $\mathbb{R}$ is carried by the finite set $s$, then for every $x \in \mathbb{R}$,
$\mu((-\infty, x]) = \sum_{y\in s,\,y\le x}\mu(\{y\})$. -/
theorem measureReal_Iic_eq_sum {μ : Measure ℝ} [IsFiniteMeasure μ]
    {s : Finset ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ s) (x : ℝ) :
    μ.real (Set.Iic x) = ∑ y ∈ s with y ≤ x, μ.real {y} := by
  have hae : Set.Iic x =ᵐ[μ] ⋃ y ∈ s.filter (· ≤ x), ({y} : Set ℝ) := by
    filter_upwards [hμ] with ω hω
    change (ω ∈ Set.Iic x) = (ω ∈ ⋃ y ∈ s.filter (· ≤ x), ({y} : Set ℝ))
    simp only [Set.mem_Iic, Set.mem_iUnion, Finset.mem_filter, Set.mem_singleton_iff,
      exists_prop, exists_eq_right', hω, true_and]
  rw [measureReal_congr hae,
    measureReal_biUnion_finset (fun a _ b _ hab => Set.disjoint_singleton.2 hab)
      (fun _ _ => measurableSet_singleton _) (fun _ _ => measure_ne_top _ _)]

/-- **Lipschitz test functions against finitely supported measures.** If the finite measures
$\mu$, $\nu$ on $\mathbb{R}$ are carried by a finite set $s \subseteq [a, b]$, $a \le b$, their
distribution functions differ by at most $K \ge 0$ at every point of $s$, and $f$ is
$L$-Lipschitz on $[a, b]$, then
$$\Bigl\lvert\int f\,d\mu - \int f\,d\nu\Bigr\rvert \le (\lvert f(b)\rvert + L(b - a))K\,;$$
for equal masses the term $\lvert f(b)\rvert$ can be removed by applying the theorem to
$f - f(b)$. This is the one-dimensional Kantorovich–Rubinstein inequality weakened to the sup
norm, with the mass difference kept as the $\lvert f(b)\rvert$ term, for finite support.
No printed source. -/
theorem abs_integral_sub_integral_le_of_lipschitzOnWith {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Finset ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ s)
    (hν : ∀ᵐ x ∂ν, x ∈ s) {a b : ℝ} (hs : ∀ x ∈ s, x ∈ Set.Icc a b) (hab : a ≤ b)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc a b)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ s, |μ.real (Set.Iic x) - ν.real (Set.Iic x)| ≤ K) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (|f b| + L * (b - a)) * K := by
  rw [integral_eq_sum_measureReal_singleton_mul hμ f,
    integral_eq_sum_measureReal_singleton_mul hν f, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, mul_comm _ (f _)]
  refine Finset.abs_sum_mul_le_of_lipschitzOnWith hs hab hf (fun y => μ.real {y} - ν.real {y})
    hK0 fun x hx => ?_
  rw [Finset.sum_sub_distrib, ← measureReal_Iic_eq_sum hμ x, ← measureReal_Iic_eq_sum hν x]
  exact hK x hx

end MeasureTheory
