/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative

/-!
# The top iterated derivative of a polynomial

The $n$-th derivative of a polynomial of degree $n$ is the constant $n!$ times its leading
coefficient. It is the step of every interpolation remainder that reads off the constant of a
monic nodal polynomial. Upstream candidate for `Mathlib.Algebra.Polynomial.Derivative`.

Design: `docs/design/Polynomial-QuadratureRemainder.md`, F1.

## Main results

* `Polynomial.iterate_derivative_natDegree`: $p^{(n)} = n!\,c_n$.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- The top derivative of a polynomial: for $p$ of degree $n$ with leading coefficient $c_n$,
the $n$-th derivative of $p$ is the constant polynomial $n!\,c_n$. -/
theorem iterate_derivative_natDegree (p : R[X]) :
    derivative^[p.natDegree] p = C ((p.natDegree.factorial : R) * p.leadingCoeff) := by
  have hdeg : (derivative^[p.natDegree] p).natDegree ≤ 0 := by
    simpa using natDegree_iterate_derivative p p.natDegree
  rw [eq_C_of_natDegree_le_zero hdeg]
  congr 1
  rw [coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rfl

end Polynomial
