/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Grid

/-!
# Exact integer literals on a fixed grid (scaffold)

Statements for `NLAlib/Computation/Grid.lean` (stage COMPDYN M2, design note
`docs/design/Computation-DynamicPrograms.md`, §4.1 and "S1 implementation status"): the grid
semantics with $t$ significant bits has exact integer literals below $2^t$.

## Main results

* `NLAlib.Computation.isExactIntLit_gridSem`: exact integer literals of the grid semantics.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P : Type}

/-- **The grid semantics has exact integer literals**: if every natural number up to $B$ is below
$2^{t(p)}$ at every tag $p$, then `NLAlib.Computation.gridSem t`, with the identity decoding,
meets `NLAlib.Computation.IsExactIntLit` at $B$: the literal of $k \le B$ rounds to itself.
No printed source.
Proof: `intro p k hk`; the literal is `some (Real.roundNearest (t p) ((k : ℚ) : ℝ))`; `k` is on
`Real.floatGrid (t p)` with mantissa `k` and exponent `0` (`|(k : ℤ)| < 2 ^ t p` from `hB p` and
`hk`, `zpow_zero`, `mul_one`), so `Real.roundNearest_eq_self_of_mem_floatGrid` gives the value
`k` (`Rat.cast_natCast`). S, about 8 lines. -/
theorem isExactIntLit_gridSem (t : P → ℕ) (B : ℕ) (hB : ∀ p, B < 2 ^ t p) :
    IsExactIntLit (fun _ x => x) (gridSem t) B := by
  sorry

end NLAlib.Computation
