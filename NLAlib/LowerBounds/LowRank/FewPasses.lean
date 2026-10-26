/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Basic

/-!
# Lower bounds for few-pass low-rank approximation: the hard spectrum

The hard instances of the pass lower bounds for rank-$k$ approximation are
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ with $\mathbf{U}$
Haar and $\mathbf{d}$ = `equispacedLevelSpectrum k m p`: a head of $k$ eigenvalues $p + 2$ and a
tail of $p + 1$ equispaced levels $1, \dots, p + 1$ with $m$ eigenvalues each. A $p$-pass
algorithm sees $\mathbf{U}$ only through polynomials of degree at most $p$ in
$\operatorname{diag}(\mathbf{d})$, and such a polynomial is fixed at the head by its values on the
tail levels (finite differences), so the head cannot be captured unless the number of products is
of the order of $m$. The statements (two passes, $p = 2$) are in the scaffold; design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.6, research note OP5.

## Main definitions

* `NLAlib.equispacedLevelSpectrum`.
-/

@[expose] public section

namespace NLAlib

/-- The **equispaced-level spectrum** with head $k$ and tail $m$ for $p$ passes, on
$k \oplus (\{0, \dots, p\} \times m)$: the value $p + 2$ on the head coordinates and $j + 1$ on
the tail level $j$. For $p = 2$ it is
$\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$, whose best
rank-$\lvert k \rvert$ Frobenius error is $14\lvert m \rvert$. -/
def equispacedLevelSpectrum (k m : Type*) (p : ℕ) : k ⊕ (Fin (p + 1) × m) → ℝ :=
  Sum.elim (fun _ => (p : ℝ) + 2) fun x => (x.1 : ℝ) + 1

end NLAlib
