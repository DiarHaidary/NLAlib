/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import NLAlib.Polynomial.Interpolation.DividedDifference

/-!
# Finite differences on equispaced nodes (scaffold)

Statement for `NLAlib/Polynomial/Interpolation/DividedDifference.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.3): the $n$-th finite difference on
equispaced nodes annihilates every polynomial of degree less than $n$. On the levels
$x, x + h, \dots, x + nh$ of a hard spectrum this is the extrapolation that limits what a
$p$-pass algorithm can separate (the value at one level is fixed by the values at the others,
for polynomials of degree at most $p$): $p(4) = p(1) - 3p(2) + 3p(3)$ for degree at most $2$.

## Main results

* `NLAlib.sum_neg_one_pow_mul_choose_mul_eval_eq_zero`.
-/

@[expose] public section

open Polynomial Finset

namespace NLAlib

/-- Finite differences annihilate low-degree polynomials: for a polynomial $P$ over a
commutative ring with $\deg P < n$ and any $x$, $h$,
$$\sum_{j=0}^{n} (-1)^{n-j}\binom{n}{j} P(x + jh) = 0 \,.$$
The equispaced case of `NLAlib.dividedDifference_eval_eq_zero`, with integer weights.
Proof: apply `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` to
$Q = P \circ (x + hX)$, whose `natDegree` is at most that of $P$
(`Polynomial.natDegree_comp_le`), at $0$, and expand the iterated difference with
`fwdDiff_iter_eq_sum_shift` (step $1$); `Polynomial.eval_comp`, `zsmul_eq_mul`, `nsmul_eq_mul`.
S, about 12 lines. -/
theorem sum_neg_one_pow_mul_choose_mul_eval_eq_zero {R : Type*} [CommRing R] {P : R[X]}
    {n : ℕ} (hP : P.natDegree < n) (x h : R) :
    ∑ j ∈ range (n + 1), (-1 : R) ^ (n - j) * (n.choose j : R) * P.eval (x + j * h) = 0 := by
  sorry

end NLAlib
