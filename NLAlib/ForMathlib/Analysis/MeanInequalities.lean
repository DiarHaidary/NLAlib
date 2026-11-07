/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# The Paley–Zygmund inequality for finite weighted sums

For weights $w_i \ge 0$ summing to $1$ and values $x_i \ge 0$, the weight of the event
$x_i > t\sum_j w_jx_j$ is at least $(1 - t)^2(\sum_i w_ix_i)^2/\sum_i w_ix_i^2$. The measure form
is `ProbabilityTheory.sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt` in
`NLAlib.ForMathlib.Probability.Moments.PaleyZygmund`; the finite form lets the matrix files work
with finite weighted sums and no measure theory. Upstream candidate for
`Mathlib/Analysis/MeanInequalities.lean`, next to the weighted power-mean inequalities.

## Main results

* `Finset.sq_mul_sq_sum_le_sum_mul_sq_mul_sum_filter`: the finite weighted Paley–Zygmund
  inequality.
-/

@[expose] public section

namespace Finset

/-- **The Paley–Zygmund inequality for finite weighted sums.** For a finite family of weights
$w_i \ge 0$ with $\sum_i w_i = 1$, values $x_i \ge 0$ and $0 \le t \le 1$,
$$(1 - t)^2\Bigl(\sum_i w_ix_i\Bigr)^2 \le \Bigl(\sum_i w_ix_i^2\Bigr)
\sum_{i \,:\, x_i > t\sum_j w_jx_j} w_i\,.$$
[PaleyZygmund1932, Lemma 19], in its discrete form. -/
theorem sq_mul_sq_sum_le_sum_mul_sq_mul_sum_filter {ι : Type*} (s : Finset ι) {w x : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 ≤ x i) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) ^ 2 * (∑ i ∈ s, w i * x i) ^ 2 ≤
      (∑ i ∈ s, w i * x i ^ 2) *
        ∑ i ∈ s.filter (fun i => t * ∑ j ∈ s, w j * x j < x i), w i := by
  set m := ∑ j ∈ s, w j * x j with hm_def
  have hm : 0 ≤ m := sum_nonneg fun i hi => mul_nonneg (hw i hi) (hx i hi)
  set A := s.filter (fun i => t * m < x i) with hA_def
  have hsplit : ∑ i ∈ s.filter (fun i => ¬ t * m < x i), w i * x i
      + ∑ i ∈ A, w i * x i = m := by
    rw [add_comm]
    exact Finset.sum_filter_add_sum_filter_not s (fun i => t * m < x i) (fun i => w i * x i)
  have hlow : ∑ i ∈ s.filter (fun i => ¬ t * m < x i), w i * x i ≤ t * m := by
    have h1 : ∑ i ∈ s.filter (fun i => ¬ t * m < x i), w i * x i
        ≤ ∑ i ∈ s.filter (fun i => ¬ t * m < x i), t * m * w i :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_filter, not_lt] at hi
        rw [mul_comm (w i)]
        exact mul_le_mul_of_nonneg_right hi.2 (hw i hi.1)
    rw [← Finset.mul_sum] at h1
    have h2 : ∑ i ∈ s.filter (fun i => ¬ t * m < x i), w i ≤ 1 := by
      have := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun i => ¬ t * m < x i) s) (fun i hi _ => hw i hi)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg ht0 hm)]
  have hlow' : (1 - t) * m ≤ ∑ i ∈ A, w i * x i := by linarith
  have hCS : (∑ i ∈ A, w i * x i) ^ 2 ≤ (∑ i ∈ A, w i) * ∑ i ∈ A, w i * x i ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A
      (fun i hi => hw i (Finset.mem_filter.1 hi).1)
      (fun i hi => mul_nonneg (hw i (Finset.mem_filter.1 hi).1) (sq_nonneg _))
      (fun i _ => le_of_eq (by ring))
  have hsub : ∑ i ∈ A, w i * x i ^ 2 ≤ ∑ i ∈ s, w i * x i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ => mul_nonneg (hw i hi) (sq_nonneg _))
  have hAw : 0 ≤ ∑ i ∈ A, w i := sum_nonneg fun i hi => hw i (Finset.mem_filter.1 hi).1
  have hfin : (∑ i ∈ A, w i) * ∑ i ∈ A, w i * x i ^ 2
      ≤ (∑ i ∈ A, w i) * ∑ i ∈ s, w i * x i ^ 2 :=
    mul_le_mul_of_nonneg_left hsub hAw
  have hsq := pow_le_pow_left₀ (mul_nonneg (by linarith) hm) hlow' 2
  rw [mul_pow] at hsq
  rw [mul_comm]
  linarith

end Finset
