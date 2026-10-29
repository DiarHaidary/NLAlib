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
* `Real.roundNearest_roundNearest`: rounding is idempotent, for $t \ge 1$.
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
  rcases eq_or_ne x 0 with rfl | hx
  · simp [roundNearest]
  have hk : (2 : ℝ) ^ Int.log 2 |x| ≤ |x| := by
    exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr hx)
  set k := Int.log 2 |x|
  have he : (0 : ℝ) < 2 ^ (k + 1 - t) := zpow_pos two_pos _
  unfold roundNearest
  have h1 : x - round (x / 2 ^ (k + 1 - t)) * 2 ^ (k + 1 - t) =
      (x / 2 ^ (k + 1 - t) - round (x / 2 ^ (k + 1 - t))) * 2 ^ (k + 1 - t) := by
    field_simp
  rw [h1, abs_mul, abs_of_pos he]
  have h2 : (1 / 2 : ℝ) * 2 ^ (k + 1 - t) = 2⁻¹ ^ t * 2 ^ k := by
    rw [zpow_sub₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, inv_pow]
    field_simp
  calc |x / 2 ^ (k + 1 - t) - round (x / 2 ^ (k + 1 - t))| * 2 ^ (k + 1 - t)
      ≤ 1 / 2 * 2 ^ (k + 1 - t) := by gcongr; exact abs_sub_round _
    _ = 2⁻¹ ^ t * 2 ^ k := h2
    _ ≤ 2⁻¹ ^ t * |x| := by gcongr

/-- Rounding lands on the grid: for $t \ge 1$, $\mathrm{fl}(x)$ is a $t$-bit floating-point
number. (For $t = 0$ the grid is $\{0\}$ and rounding can give a power of two.) No printed
source. -/
theorem roundNearest_mem_floatGrid {t : ℕ} (ht : 0 < t) (x : ℝ) :
    roundNearest t x ∈ floatGrid t := by
  have hlt : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := by
    exact_mod_cast Int.lt_zpow_succ_log_self (b := 2) one_lt_two |x|
  set k := Int.log 2 |x|
  set e : ℤ := k + 1 - t
  have he : (0 : ℝ) < 2 ^ e := zpow_pos two_pos _
  set y := x / 2 ^ e
  have hy : |y| < 2 ^ t := by
    rw [abs_div, abs_of_pos he, div_lt_iff₀ he, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
    simpa [e] using hlt
  -- `|round y| ≤ 2 ^ t`
  have hr : |round y| ≤ (2 : ℤ) ^ t := by
    have hy' := abs_lt.mp hy
    have hu : round y < (2 : ℤ) ^ t + 1 := by
      have := round_le_add_half y
      have : ((round y : ℤ) : ℝ) < ((2 ^ t + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hl : -(2 : ℤ) ^ t - 1 < round y := by
      have := sub_half_lt_round y
      have : ((-(2 : ℤ) ^ t - 1 : ℤ) : ℝ) < ((round y : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    rw [abs_le]; constructor <;> omega
  rcases hr.lt_or_eq with hr | hr
  · exact ⟨round y, e, hr, rfl⟩
  · have h1 : (1 : ℤ) < 2 ^ t := one_lt_pow₀ one_lt_two ht.ne'
    have hry : round y = 2 ^ t ∨ round y = -2 ^ t := by
      rcases le_or_gt 0 (round y) with h | h
      · left; rw [abs_of_nonneg h] at hr; exact hr
      · right; rw [abs_of_neg h] at hr; omega
    change (round y : ℝ) * 2 ^ e ∈ floatGrid t
    rcases hry with h | h
    · refine ⟨1, e + t, by simpa using h1, ?_⟩
      rw [h, zpow_add₀ two_ne_zero, zpow_natCast]; push_cast; ring
    · refine ⟨-1, e + t, by simpa using h1, ?_⟩
      rw [h, zpow_add₀ two_ne_zero, zpow_natCast]; push_cast; ring

/-- Rounding fixes the grid: a $t$-bit floating-point number $x$ rounds to itself. No printed
source. -/
theorem roundNearest_eq_self_of_mem_floatGrid {t : ℕ} {x : ℝ} (hx : x ∈ floatGrid t) :
    roundNearest t x = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [roundNearest]
  obtain ⟨m, e', hm, rfl⟩ := hx
  have hk : (2 : ℝ) ^ Int.log 2 |(m : ℝ) * 2 ^ e'| ≤ |(m : ℝ) * 2 ^ e'| := by
    exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr hx0)
  set k := Int.log 2 |(m : ℝ) * 2 ^ e'|
  have hm' : |(m : ℝ)| < 2 ^ t := by exact_mod_cast hm
  have hlt : |(m : ℝ) * 2 ^ e'| < 2 ^ (e' + t) := by
    rw [abs_mul, abs_of_pos (zpow_pos (two_pos (α := ℝ)) e'), zpow_add₀ two_ne_zero,
      zpow_natCast]
    exact mul_lt_mul_of_pos_right hm' (zpow_pos two_pos _) |>.trans_eq (mul_comm _ _)
  have hke : k + 1 - t ≤ e' := by
    by_contra h
    have : (2 : ℝ) ^ (e' + t) ≤ 2 ^ k := zpow_le_zpow_right₀ one_le_two (by omega)
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, e' = k + 1 - t + n := ⟨(e' - (k + 1 - t)).toNat, by omega⟩
  change (round ((m : ℝ) * 2 ^ e' / (2 : ℝ) ^ (k + 1 - t)) : ℝ) * (2 : ℝ) ^ (k + 1 - t) = _
  have hq : (m : ℝ) * 2 ^ e' / 2 ^ (k + 1 - t) = ((m * 2 ^ n : ℤ) : ℝ) := by
    rw [hn, zpow_add₀ two_ne_zero, zpow_natCast]
    push_cast
    field_simp
  rw [hq, round_intCast, ← hq]
  field_simp

/-- Rounding is idempotent for $t \ge 1$: $\mathrm{fl}(\mathrm{fl}(x)) = \mathrm{fl}(x)$, as
$\mathrm{fl}(x)$ is on the grid. No printed source. -/
theorem roundNearest_roundNearest {t : ℕ} (ht : 0 < t) (x : ℝ) :
    roundNearest t (roundNearest t x) = roundNearest t x :=
  roundNearest_eq_self_of_mem_floatGrid (roundNearest_mem_floatGrid ht x)

/-- The grid is symmetric: if $x$ is a $t$-bit floating-point number, so is $-x$. No printed
source. -/
theorem neg_mem_floatGrid {t : ℕ} {x : ℝ} (hx : x ∈ floatGrid t) : -x ∈ floatGrid t := by
  obtain ⟨m, e, hm, rfl⟩ := hx
  exact ⟨-m, e, by rwa [abs_neg], by push_cast; ring⟩

end Real
