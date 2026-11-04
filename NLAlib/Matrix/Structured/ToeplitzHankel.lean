/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Toeplitz and Hankel matrices

The entries depend on the ordinary difference or sum of the row and column indices.
The constructors allow rectangular shapes and any entry type.
Adapted from tchen-research/NLAlib at `77514ce42a0e437d837797a063ac161f41022730`.

## Main definitions

* `NLAlib.toeplitzMatrix`: entries constant along diagonals.
* `NLAlib.hankelMatrix`: entries constant along anti-diagonals.

## Main results

Both entry formulas hold by definition.
-/

@[expose] public section

namespace NLAlib

/-- The **Toeplitz matrix** with diagonal parameters $t_d$ has entry $t_{j-i}$ in row $i$ and
column $j$. The indices start at zero and the difference is an integer.
[HornJohnson2013, §0.9.7]. -/
def toeplitzMatrix {R : Type*} {m n : ℕ} (t : ℤ → R) : Matrix (Fin m) (Fin n) R :=
  Matrix.of fun i j => t ((j.val : ℤ) - (i.val : ℤ))

/-- The **Hankel matrix** with anti-diagonal parameters $h_d$ has entry $h_{i+j}$ in row $i$
and column $j$, with both indices starting at zero.
[HornJohnson2013, §0.9.8]. -/
def hankelMatrix {R : Type*} {m n : ℕ} (h : ℕ → R) : Matrix (Fin m) (Fin n) R :=
  Matrix.of fun i j => h (i.val + j.val)

end NLAlib
