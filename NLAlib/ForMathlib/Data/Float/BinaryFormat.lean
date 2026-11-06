/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.ForMathlib.Algebra.Order.Round

/-!
# Binary grids with a lower exponent

Upstream candidates for the mathematical API of Lean core's floating-point model.
Adapted from the supplied NumLean archive, `NumLean/Mathlib/Rounding/BinaryFormat.lean`.
The archive's SHA-256 and licensing status, the earlier Mathlib search and the changes for Lean 4.33
are recorded in `docs/design/Finite-Precision-Arithmetic.md`. No NumLean dependency is imported.
General format lemmas state a two-exponent-bit assumption explicitly where needed; core 4.33
also permits one-bit layouts. These results concern logical arithmetic, not native execution cost.

## Main results

* `Float.Model.BinaryRounding.IsBinaryFloat.mem_floatGrid`.
* `Float.Model.BinaryRounding.IsNearestFloat.abs_le_of_abs_le`.
* `Float.Model.BinaryRounding.isNearestFloat_of_lattice`.
-/

@[expose] public section

namespace Float.Model.BinaryRounding

/-- A real value has a binary representation $x=M2^e$ with integer significand
$\lvert M\rvert<2^p$ and exponent $e\ge e_{\min}$. There is no upper exponent bound. -/
def IsBinaryFloat (p : ℕ) (emin : ℤ) (x : ℝ) : Prop :=
  ∃ M e : ℤ, emin ≤ e ∧ |M| < 2 ^ p ∧ x = M * 2 ^ e

/-- A represented value is nearest to a real input if it is at least as close as every
represented value of the lower-exponent format.
Ties are broken in any way, so this covers round-to-nearest-even without stating the tie rule. -/
def IsNearestFloat (p : ℕ) (emin : ℤ) (x r : ℝ) : Prop :=
  IsBinaryFloat p emin r ∧ ∀ y, IsBinaryFloat p emin y → |r - x| ≤ |y - x|

variable {p : ℕ} {emin : ℤ}

/-! ### Floats -/

/-- Zero belongs to every lower-exponent binary grid. -/
theorem isBinaryFloat_zero : IsBinaryFloat p emin 0 :=
  ⟨0, emin, le_rfl, by simp, by simp⟩

/-- Negation preserves the significand bound and lower exponent bound. -/
theorem IsBinaryFloat.neg {x : ℝ} (h : IsBinaryFloat p emin x) : IsBinaryFloat p emin (-x) := by
  obtain ⟨M, e, he, hM, rfl⟩ := h
  exact ⟨-M, e, he, by simpa using hM, by push_cast; ring⟩

/-- A binary multiple at exponent $e$ is an integral lattice multiple at every exponent $t\le e$. -/
theorem int_mul_two_zpow_eq_of_le (M : ℤ) {e t : ℤ} (h : t ≤ e) :
    (M : ℝ) * 2 ^ e = ((M * 2 ^ (e - t).toNat : ℤ) : ℝ) * 2 ^ t := by
  push_cast
  rw [mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ two_ne_zero]
  congr 2
  ring

/-! ### Nearest floats -/

/-- A nearest represented value belongs to the stated lower-exponent binary grid. -/
theorem IsNearestFloat.isBinaryFloat {x r : ℝ} (h : IsNearestFloat p emin x r) :
    IsBinaryFloat p emin r :=
  h.1

/-- A float rounds to itself. -/
theorem IsNearestFloat.eq_of_isBinaryFloat {x r : ℝ} (h : IsNearestFloat p emin x r)
    (hx : IsBinaryFloat p emin x) : r = x := by
  have := h.2 x hx
  simp only [sub_self, abs_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- A represented value is a nearest grid value to itself. -/
theorem isNearestFloat_self {x : ℝ} (hx : IsBinaryFloat p emin x) : IsNearestFloat p emin x x :=
  ⟨hx, fun y _ => by simp⟩

/-- Negating the input and output preserves nearest rounding, independently of the tie policy. -/
theorem IsNearestFloat.neg {x r : ℝ} (h : IsNearestFloat p emin x r) :
    IsNearestFloat p emin (-x) (-r) := by
  refine ⟨h.1.neg, fun y hy => ?_⟩
  have := h.2 (-y) hy.neg
  calc |-r - -x| = |r - x| := by rw [← abs_neg]; ring_nf
    _ ≤ |-y - x| := this
    _ = |y - -x| := by rw [← abs_neg]; ring_nf

/-- A nearest represented value never exceeds a represented upper bound on its real input. -/
theorem IsNearestFloat.le_of_le {x y r : ℝ} (h : IsNearestFloat p emin x r)
    (hy : IsBinaryFloat p emin y) (hxy : x ≤ y) : r ≤ y := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  have := h.2 y hy
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
  linarith

/-- A nearest represented value is never below a represented lower bound on its real input. -/
theorem IsNearestFloat.ge_of_le {x y r : ℝ} (h : IsNearestFloat p emin x r)
    (hy : IsBinaryFloat p emin y) (hyx : y ≤ x) : y ≤ r := by
  have := h.neg.le_of_le hy.neg (by linarith)
  linarith

/-- Rounding a real input whose magnitude is bounded by a represented value does not exceed
that represented magnitude. -/
theorem IsNearestFloat.abs_le_of_abs_le {x y r : ℝ} (h : IsNearestFloat p emin x r)
    (hy : IsBinaryFloat p emin y) (hxy : |x| ≤ |y|) : |r| ≤ |y| := by
  have hy' : IsBinaryFloat p emin |y| := by
    rcases abs_choice y with h' | h' <;> rw [h'] <;> [exact hy; exact hy.neg]
  have h1 := h.le_of_le hy' (le_trans (le_abs_self x) hxy)
  have h2 := h.ge_of_le hy'.neg (by linarith [neg_abs_le x])
  exact abs_le.2 ⟨h2, h1⟩

/-! ### The lattice criterion -/

/-- On the lattice $2^t\mathbb{Z}$, a point within half a spacing of a real input is at least
as close to that input as every lattice point. -/
theorem abs_sub_le_of_lattice {x r z : ℝ} {t : ℤ} (hk : ∃ k : ℤ, r = k * 2 ^ t)
    (hz : ∃ k : ℤ, z = k * 2 ^ t) (hd : |r - x| ≤ 2 ^ t / 2) : |r - x| ≤ |z - x| := by
  obtain ⟨k, rfl⟩ := hk
  obtain ⟨k', rfl⟩ := hz
  have h2t : (0 : ℝ) < 2 ^ t := zpow_pos (by norm_num) _
  by_cases hkk : k = k'
  · subst hkk; exact le_rfl
  · have hne : (1 : ℝ) ≤ |(k : ℝ) - k'| := by
      have : (1 : ℤ) ≤ |k - k'| := Int.one_le_abs (sub_ne_zero.2 hkk)
      exact_mod_cast this
    have hstep : 2 ^ t ≤ |(k : ℝ) * 2 ^ t - k' * 2 ^ t| := by
      rw [← sub_mul, abs_mul, abs_of_pos h2t]
      nlinarith
    have := abs_sub_le ((k : ℝ) * 2 ^ t) x ((k' : ℝ) * 2 ^ t)
    rw [abs_sub_comm x] at this
    linarith [abs_sub_comm ((k : ℝ) * 2 ^ t) x]

/-- A represented lattice point within half a spacing of an input is a nearest grid value
if the lattice is the smallest-exponent lattice, or if $2^{t+p-1}\le\lvert x\rvert$.
The precision satisfies $p\ge1$, and the lattice exponent satisfies $t\ge e_{\min}$. -/
theorem isNearestFloat_of_lattice {x r : ℝ} {t : ℤ} (hp : 1 ≤ p) (ht : emin ≤ t)
    (hx : t = emin ∨ 2 ^ (t + p - 1) ≤ |x|) (hr : IsBinaryFloat p emin r)
    (hk : ∃ k : ℤ, r = k * 2 ^ t) (hd : |r - x| ≤ 2 ^ t / 2) : IsNearestFloat p emin x r := by
  refine ⟨hr, fun y hy => ?_⟩
  obtain ⟨M, e, he, hM, rfl⟩ := hy
  by_cases hte : t ≤ e
  · exact abs_sub_le_of_lattice hk ⟨_, int_mul_two_zpow_eq_of_le M hte⟩ hd
  · replace hte := not_le.1 hte
    have hx' : (2 : ℝ) ^ (t + p - 1) ≤ |x| := by
      rcases hx with rfl | hx
      · omega
      · exact hx
    have hM' : |(M : ℝ)| < 2 ^ p := by exact_mod_cast hM
    -- the float `y` is smaller than the lattice point `z` of the same sign as `x`
    have hy : |(M : ℝ) * 2 ^ e| ≤ 2 ^ (t + p - 1) := by
      calc |(M : ℝ) * 2 ^ e| = |(M : ℝ)| * 2 ^ e := by
            rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) _)]
        _ ≤ 2 ^ p * 2 ^ e :=
            mul_le_mul_of_nonneg_right hM'.le (zpow_pos (by norm_num : (0:ℝ) < 2) _).le
        _ = 2 ^ ((p : ℤ) + e) := by rw [zpow_add₀ two_ne_zero, zpow_natCast]
        _ ≤ 2 ^ (t + p - 1) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hpow : (2 : ℝ) ^ (t + p - 1) = ((2 ^ (p - 1) : ℤ) : ℝ) * 2 ^ t := by
      push_cast
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, add_comm]
      congr 1
      omega
    have hz : ∃ z : ℝ, (∃ k : ℤ, z = k * 2 ^ t) ∧ |z - x| = |x| - 2 ^ (t + p - 1) := by
      rcases le_total 0 x with hx0 | hx0
      · refine ⟨2 ^ (t + p - 1), ⟨2 ^ (p - 1), hpow⟩, ?_⟩
        rw [abs_of_nonneg hx0] at hx' ⊢
        rw [abs_of_nonpos (by linarith)]
        ring
      · refine ⟨-2 ^ (t + p - 1), ⟨-2 ^ (p - 1), by rw [Int.cast_neg, neg_mul, hpow]⟩, ?_⟩
        rw [abs_of_nonpos hx0] at hx' ⊢
        rw [abs_of_nonneg (by linarith)]
        ring
    obtain ⟨z, hz1, hz2⟩ := hz
    have h1 := abs_sub_le_of_lattice hk hz1 hd
    have h2 : |x| - |(M : ℝ) * 2 ^ e| ≤ |(M : ℝ) * 2 ^ e - x| := by
      rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    linarith

/-- A lower-exponent binary grid is contained in the existing unbounded-exponent grid.
This transports representability only, not a tie-breaking rule or an arithmetic implementation. -/
theorem IsBinaryFloat.mem_floatGrid {x : ℝ} (h : IsBinaryFloat p emin x) :
    x ∈ Real.floatGrid p := by
  obtain ⟨m, e, _, hm, hx⟩ := h
  exact ⟨m, e, hm, hx⟩

end Float.Model.BinaryRounding
