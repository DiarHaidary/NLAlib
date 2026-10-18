/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import NLAlib.ForMathlib.Analysis.Convex.SupportingLine

/-!
# Chebyshev filters with supporting lines

The squared Chebyshev filter of randomized block Krylov iteration,
$\varphi_j(y) = y\,T_j(2y - 1)^2 = y\,T_{2j}(\sqrt{y})^2$, is not convex on $[0, \infty)$, but it
has a supporting line on $[0, \infty)$ at every point $x \ge 1$: on $[0, 1]$ its derivative is at
most $\varphi_j'(1)$, and on $[1, \infty)$ it is convex. This is what lets Jensen's inequality pass
through the filter in the gapless bound for randomized block Krylov iteration
(`HasSupportingLineOn.le_integral_comp`).

## Main results

* `NLAlib.hasSupportingLineOn_mul_eval_T_sq`: the supporting lines of $y\,T_j(2y - 1)^2$.
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

-- Stage B2b

/-- **Supporting lines of the squared Chebyshev filter**: for every $j$ and every $x \ge 1$, the
function $\varphi(y) = y\,T_j(2y - 1)^2$ has a supporting line on $[0, \infty)$ at $x$. Since
$T_j(2y - 1) = T_{2j}(\sqrt{y})$, this is the filter $y\,T_{2j}(\sqrt{y})^2$ of the source.
[TroppWebber2023, Lemma 9.3], part 5; there for $x\,T_{2j}(x^{1/2})^2$ (the $x^{1/4}$ variant of the
source is not needed). -/
theorem hasSupportingLineOn_mul_eval_T_sq (j : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    HasSupportingLineOn (fun y => y * ((T ℝ (j : ℤ)).eval (2 * y - 1)) ^ 2) (Set.Ici 0) x := by
  sorry

end NLAlib
