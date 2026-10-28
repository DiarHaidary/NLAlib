/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Int.Log
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Rounding to a binary floating-point grid

The binary floating-point numbers with $t$ significant bits and unbounded exponent,
`Real.floatGrid t` (the numbers $m 2^e$ with integers $\lvert m \rvert < 2^t$ and $e$), and
rounding to nearest onto it, `Real.roundNearest t x`: scale $x$ by the power of two that puts
$\lvert x \rvert$ in $[2^{t-1}, 2^t)$ (through `Int.log`), round to an integer with Mathlib's
`round` (ties upward) and scale back. The relative error is at most $u = 2^{-t}$
[Higham2002, Theorem 2.2]. Mathlib's `FP` (`Mathlib.Data.FP.Basic`) is an experimental
implementation of floating-point numbers with no theorems about rounding; nothing here reuses it.
Upstream candidate for `Mathlib.Algebra.Order.Round`. Design:
`docs/design/Computation-Rounding.md` (R7).

## Main definitions

* `Real.floatGrid`: the grid of $t$-bit binary floating-point numbers.
* `Real.roundNearest`: rounding to nearest onto it.

## Main results

* `Real.abs_sub_roundNearest_le`: $\lvert x - \mathrm{fl}(x) \rvert \le 2^{-t} \lvert x \rvert$.
* `Real.roundNearest_mem_floatGrid`: rounding lands on the grid, for $t \ge 1$.
* `Real.roundNearest_eq_self_of_mem_floatGrid`: rounding fixes the grid.
* `Real.neg_mem_floatGrid`: the grid is symmetric.
-/

@[expose] public section

namespace Real

/-- **The binary floating-point grid** with $t$ significant bits and unbounded exponent: the real
numbers $m 2^e$ with integers $m$, $e$ and $\lvert m \rvert < 2^t$ (so $0$ is on it). -/
def floatGrid (t : ℕ) : Set ℝ := {x | ∃ m e : ℤ, |m| < 2 ^ t ∧ x = m * (2 : ℝ) ^ e}

/-- **Rounding to nearest** onto `Real.floatGrid t`: with $k = \lfloor \log_2 \lvert x \rvert
\rfloor$ (`Int.log`) and $e = k + 1 - t$, the integer nearest to $x 2^{-e}$ (Mathlib's `round`,
ties upward) times $2^e$. At $x = 0$ it is $0$. -/
noncomputable def roundNearest (t : ℕ) (x : ℝ) : ℝ :=
  round (x / (2 : ℝ) ^ (Int.log 2 |x| + 1 - t)) * (2 : ℝ) ^ (Int.log 2 |x| + 1 - t)

/-- **The rounding error bound** [Higham2002, Theorem 2.2]: rounding to nearest onto the grid
with $t$ significant bits has relative error at most $u = 2^{-t}$,
$\lvert x - \mathrm{fl}(x) \rvert \le 2^{-t} \lvert x \rvert$. -/
theorem abs_sub_roundNearest_le (t : ℕ) (x : ℝ) :
    |x - roundNearest t x| ≤ 2⁻¹ ^ t * |x| := by
  sorry

/-- **Rounding lands on the grid**: for $t \ge 1$, $\mathrm{fl}(x)$ is a $t$-bit floating-point
number. (For $t = 0$ the grid is $\{0\}$ and rounding can give a power of two.) No printed
source. -/
theorem roundNearest_mem_floatGrid {t : ℕ} (ht : 0 < t) (x : ℝ) :
    roundNearest t x ∈ floatGrid t := by
  sorry

/-- **Rounding fixes the grid**: a $t$-bit floating-point number $x$ rounds to itself. No printed
source. -/
theorem roundNearest_eq_self_of_mem_floatGrid {t : ℕ} {x : ℝ} (hx : x ∈ floatGrid t) :
    roundNearest t x = x := by
  sorry

/-- **The grid is symmetric**: if $x$ is a $t$-bit floating-point number, so is $-x$. No printed
source. -/
theorem neg_mem_floatGrid {t : ℕ} {x : ℝ} (hx : x ∈ floatGrid t) : -x ∈ floatGrid t := by
  obtain ⟨m, e, hm, rfl⟩ := hx
  exact ⟨-m, e, by rwa [abs_neg], by push_cast; ring⟩

end Real
