/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Degree of a Chebyshev polynomial composed with an affine map

$T_n \circ p$ has degree at most $\lvert n \rvert$ when $p$ has degree at most $1$: the degree
count behind every shifted Chebyshev filter $T_n(2x/s - 1)$ and every normalized Chebyshev
residual. Upstream candidate for `Mathlib/RingTheory/Polynomial/Chebyshev.lean`, beside
`Polynomial.Chebyshev.natDegree_T`.

Design: consolidation round (`docs/design/Consolidation.md` §3.1, F5).

## Main results

* `Polynomial.Chebyshev.natDegree_T_comp_le`.
-/

@[expose] public section

namespace Polynomial.Chebyshev

open Polynomial

/-- The Chebyshev polynomial $T_n$ composed with a polynomial $p$ of degree at most $1$ has
degree at most $\lvert n \rvert$. Upstream candidate. -/
theorem natDegree_T_comp_le {R : Type*} [CommRing R] [IsDomain R] [NeZero (2 : R)] (n : ℤ)
    {p : R[X]} (hp : p.natDegree ≤ 1) : ((T R n).comp p).natDegree ≤ n.natAbs := by
  refine natDegree_comp_le.trans ?_
  rw [natDegree_T]
  exact (Nat.mul_le_mul_left _ hp).trans_eq (mul_one _)

end Polynomial.Chebyshev
