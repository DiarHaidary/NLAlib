/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Nat.Init

/-!
# Flat column-major indices

The flat index $i + Nj$ of entry $(i, j)$ of a column-major block with $N$ rows determines
$(i, j)$ when $i < N$. Upstream candidate for `Mathlib.Data.Nat.Init`; the block bound
$i + Nj < Nk$ is Batteries' `Nat.add_mul_lt_mul_of_lt_of_lt`.

## Main results

* `Nat.add_mul_eq_add_mul_iff_of_lt`: $i + Nj = i' + Nj'$ if and only if $i = i'$ and
  $j = j'$, for $i, i' < N$.
-/

@[expose] public section

namespace Nat

/-- Flat column-major indices are injective: for $i, i' < N$, $i + Nj = i' + Nj'$ if and only if
$i = i'$ and $j = j'$. -/
theorem add_mul_eq_add_mul_iff_of_lt {N i i' j j' : ℕ} (hi : i < N) (hi' : i' < N) :
    i + N * j = i' + N * j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
    have h1 : (i + N * j) % N = (i' + N * j') % N := by rw [h]
    have h2 : (i + N * j) / N = (i' + N * j') / N := by rw [h]
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt hi'] at h1
    rw [Nat.add_mul_div_left _ _ hN, Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hi,
      Nat.div_eq_of_lt hi'] at h2
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end Nat
