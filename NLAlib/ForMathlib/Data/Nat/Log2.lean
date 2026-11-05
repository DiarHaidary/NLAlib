/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import Init.Data.Nat.Log2
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Positivity

/-!
# Binary logarithms under shifts

Upstream candidates for the mathematical API of Lean core's floating-point model.
Adapted from the supplied NumLean archive, `NumLean/Mathlib/Data/Nat/Log2.lean`. The archive's
SHA-256 and licensing status, the earlier Mathlib search and the changes needed for Lean 4.33
are recorded in `docs/design/Finite-Precision-Arithmetic.md`. No NumLean dependency is imported.
The statement concerns natural-number binary logarithms, independently of a floating-point format
or native execution cost.

## Main results

* `Nat.log2_mul_pow`.
-/

@[expose] public section

namespace Nat

/-- Multiplication of a nonzero natural number by $2^k$ increases its binary logarithm by $k$. -/
theorem log2_mul_pow {m : ℕ} (hm : m ≠ 0) (k : ℕ) : (m * 2 ^ k).log2 = m.log2 + k := by
  have hl : 2 ^ m.log2 ≤ m ∧ m < 2 ^ (m.log2 + 1) := ⟨Nat.log2_self_le hm, Nat.lt_log2_self⟩
  rw [Nat.log2_eq_iff (by positivity)]
  constructor
  · rw [pow_add]; exact Nat.mul_le_mul_right _ hl.1
  · rw [show m.log2 + k + 1 = (m.log2 + 1) + k by omega, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hl.2 (by positivity)

end Nat
