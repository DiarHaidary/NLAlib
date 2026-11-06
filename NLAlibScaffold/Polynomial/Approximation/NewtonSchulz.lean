/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.NewtonSchulz

/-!
# Linear growth of the Newton–Schulz map near zero (scaffold, stage HDIAG-BOUNDS)

Statement for `NLAlib/Polynomial/Approximation/NewtonSchulz.lean` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, item I9): below $1/2$ the map
$g(x) = \tfrac12x(3 - x^2)$ multiplies the modulus by at least $11/8$, which makes the errors of
the matrix iteration a geometric series (SN4').

## Main results

* `NLAlib.mul_abs_le_abs_newtonSchulz_of_abs_le` (NS13).
-/

@[expose] public section

namespace NLAlib

/-- **The Newton–Schulz map grows the modulus near zero** (NS13): for $\lvert x \rvert \le 1/2$,
$\tfrac{11}{8}\lvert x \rvert \le \lvert g(x) \rvert$, since $g(x)/x = (3 - x^2)/2 \ge 11/8$.
Proof: unfold `NLAlib.newtonSchulz`; $\lvert g(x)\rvert = \lvert x\rvert(3 - x^2)/2$
(`abs_mul`, the factor is positive); `nlinarith` with $x^2 \le 1/4$ (`sq_abs`,
`abs_le`). S, about 8 lines. -/
theorem mul_abs_le_abs_newtonSchulz_of_abs_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    11 / 8 * |x| ≤ |newtonSchulz x| := by
  have hsq : x ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at h
    norm_num at h ⊢
    linarith
  have hpos : 0 < 3 - x ^ 2 := by linarith
  unfold newtonSchulz
  rw [abs_div, abs_mul, abs_of_pos hpos, abs_two]
  have h0 := abs_nonneg x
  nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 / 4 - x ^ 2)]

end NLAlib
