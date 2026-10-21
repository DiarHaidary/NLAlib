/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Real.Basic

/-!
# Sums of a non-increasing sequence over an index set

A sum of values of a non-increasing real sequence over a finite set $s$ of indices is at most
the sum of its first $\lvert s \rvert$ values. This is the partial-sum form of majorization
statements for sorted sequences, such as eigenvalues and singular values. Upstream candidate
for `Mathlib.Algebra.Order.BigOperators.Group.Finset`.

## Main results

* `Finset.sum_le_sum_range_card_of_antitone`:
  $\sum_{i \in s} f(i) \le \sum_{i < \lvert s \rvert} f(i)$ for non-increasing $f$.
-/

@[expose] public section

namespace Finset

/-- A sum of values of a non-increasing sequence over an index set $s$ is at most the sum of its
first $\lvert s \rvert$ values: $\sum_{i \in s} f(i) \le \sum_{i < \lvert s \rvert} f(i)$, with
no bound on the indices. -/
theorem sum_le_sum_range_card_of_antitone {f : ℕ → ℝ} (hf : Antitone f) (s : Finset ℕ) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ Finset.range s.card, f i := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcard : s.card ≤ a := by
      have h := Finset.card_le_card (fun i hi => Finset.mem_range.mpr (ha i hi) :
        s ⊆ Finset.range a)
      rwa [Finset.card_range] at h
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, Finset.sum_range_succ, add_comm]
    exact add_le_add ih (hf hcard)

end Finset
