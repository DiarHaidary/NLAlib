/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Greedy choice of a permutation

A permutation of `Fin n` can be built position by position, swapping into each position a
maximiser of a score that the permutations already chosen transform covariantly: the choice
of pivots in partial pivoting and in diagonally pivoted Cholesky. Upstream candidate for
`Mathlib.GroupTheory.Perm.Fin`.

## Main results

* `Fin.exists_perm_forall_le_apply_self`: greedy pivoting.
-/

@[expose] public section

namespace Fin

/-- **Greedy pivoting.** Let $s_\sigma(j, i)$ score the candidate $i$ for the pivot position $j$
after the permutation $\sigma$, and suppose that composing $\sigma$ with a permutation $\tau$
fixing the positions before $j$ permutes the scores at step $j$ by $\tau$:
$s_{\sigma \circ \tau}(j, i) = s_\sigma(j, \tau(i))$. Then some permutation $\sigma$ makes every
pivot among the first $k$ maximal over the later positions, $s_\sigma(j, i) \le s_\sigma(j, j)$ for
$j < k$ and $j \le i$: swap a maximiser into each position in turn.
This is the choice of pivots in partial pivoting and in diagonally pivoted Cholesky. -/
theorem exists_perm_forall_le_apply_self {α : Type*} [LinearOrder α] {n : ℕ}
    (s : Equiv.Perm (Fin n) → Fin n → Fin n → α)
    (hs : ∀ (σ τ : Equiv.Perm (Fin n)) (j : Fin n), (∀ l : Fin n, l < j → τ l = l) →
      ∀ i, s (τ.trans σ) j i = s σ j (τ i)) (k : ℕ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j i : Fin n, (j : ℕ) < k → j ≤ i → s σ j i ≤ s σ j j := by
  induction k with
  | zero => exact ⟨1, fun j i hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨σ, hσ⟩ := ih
    by_cases hk : k < n
    · obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.Ici (⟨k, hk⟩ : Fin n))
        (s σ ⟨k, hk⟩) ⟨_, Finset.mem_Ici.mpr le_rfl⟩
      have hi₀' : k ≤ (i₀ : ℕ) := Fin.le_def.mp (Finset.mem_Ici.mp hi₀)
      have hτ : ∀ l : Fin n, (l : ℕ) < k → Equiv.swap (⟨k, hk⟩ : Fin n) i₀ l = l := fun l hl =>
        Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp only; omega))
          (Fin.ne_of_val_ne (by omega))
      have hge : ∀ (m : ℕ) (i : Fin n), m ≤ k → m ≤ (i : ℕ) →
          m ≤ ((Equiv.swap (⟨k, hk⟩ : Fin n) i₀ i : Fin n) : ℕ) := by
        intro m i hmk hmi
        rw [Equiv.swap_apply_def]
        split_ifs
        · omega
        · exact hmk
        · exact hmi
      refine ⟨(Equiv.swap ⟨k, hk⟩ i₀).trans σ, fun j i hj hji => ?_⟩
      have hτj : ∀ l : Fin n, l < j → Equiv.swap (⟨k, hk⟩ : Fin n) i₀ l = l := fun l hl =>
        hτ l (by have := Fin.lt_def.mp hl; omega)
      rw [hs σ _ j hτj, hs σ _ j hτj]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · rw [hτ j hjk]
        exact hσ j _ hjk (Fin.le_def.mpr (hge j i hjk.le (Fin.le_def.mp hji)))
      · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hjk
        rw [Equiv.swap_apply_left]
        exact hmax _ (Finset.mem_Ici.mpr (Fin.le_def.mpr (hge k i le_rfl (Fin.le_def.mp hji))))
    · exact ⟨σ, fun j i hj hji => hσ j i (by omega) hji⟩

end Fin
