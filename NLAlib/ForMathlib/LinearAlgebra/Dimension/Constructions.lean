/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The dimension of a space of functions

The functions from a finite type $\eta$ to a finite free module $M$ have dimension
$\lvert \eta \rvert$ times the dimension of $M$, the `finrank` form of Mathlib's `rank_fun`. Over
$\mathbb{R}$, the coordinate space of $\Bbbk^n$ has real dimension $\lvert n \rvert$ for
$\Bbbk = \mathbb{R}$ and $2 \lvert n \rvert$ for $\Bbbk = \mathbb{C}$. Upstream candidate for
`Mathlib.LinearAlgebra.Dimension.Constructions`.

## Main results

* `Module.finrank_fun`: the dimension of the functions from $\eta$ to $M$ is
  $\lvert \eta \rvert$ times the dimension of $M$.
-/
@[expose] public section

namespace Module

/-- The `finrank` of the functions from a finite type to a finite free module is the number of
points times the `finrank` of the module. The `finrank` form of `rank_fun`. -/
theorem finrank_fun {R M η : Type*} [Ring R] [StrongRankCondition R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] [Fintype η] :
    finrank R (η → M) = Fintype.card η * finrank R M := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Module
