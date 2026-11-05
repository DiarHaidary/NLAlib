/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Underflow
public import Mathlib.Data.Rat.Floor

/-!
# Bounded fixed-point arithmetic

`NLAlib.Computation.FixedPoint limit` consists of integer words between the symmetric endpoints
$-\mathit{limit}$ and $\mathit{limit}$. At a positive natural scale $s$, a word $w$ decodes to
$w/s$. Addition and subtraction are exact when their integer result is in range. Multiplication,
division and rational literals round down to the grid and reject a result outside the carrier;
division by zero is rejected. This is a computable example of finite-range arithmetic other
than IEEE, using the same scalar contracts as the other backends.

The absolute rounding error is at most $1/s$, including results below one grid spacing.
Every exact arithmetic result in the closed representable interval succeeds. Square root
and bit operations are unsupported; the certificate covers `BinOp.IsArith` only.
The finite word encoding is distinct from native implementation costs: execution uses Lean's
integers and rationals, without a claimed native fixed-width cost bound.

## Main results

* `NLAlib.Computation.FixedPoint.toFin_injective`: encoding into the finite word set.
* `NLAlib.Computation.abs_sub_fixedPointDecode_le_of_fixedPointRound`: absolute rounding accuracy.
* `NLAlib.Computation.isArithErrSem_fixedPointSem`: mixed-error and range-success contract.
* `NLAlib.Computation.addsZeroExactly_fixedPointSem`: compatibility with kernel accumulation.
-/

@[expose] public section

namespace NLAlib.Computation

/-- Integer fixed-point words in the symmetric range $[-\mathit{limit},\mathit{limit}]$.
The scale is supplied by the arithmetic interpretation, not stored in each word. -/
abbrev FixedPoint (limit : ℕ) := {w : ℤ // |w| ≤ (limit : ℤ)}

/-- Encode a bounded signed integer by its offset from the lower endpoint. -/
def FixedPoint.toFin {limit : ℕ} (w : FixedPoint limit) : Fin (2 * limit + 1) :=
  ⟨(w.val + (limit : ℤ)).toNat, by have hw := abs_le.mp w.property; omega⟩

/-- Distinct fixed-point words have distinct finite encodings. -/
theorem FixedPoint.toFin_injective {limit : ℕ} :
    Function.Injective (@FixedPoint.toFin limit) := by
  intro x y h
  apply Subtype.ext
  have hx := abs_le.mp x.property
  have hy := abs_le.mp y.property
  have hval := congrArg Fin.val h
  dsimp only [FixedPoint.toFin] at hval
  omega

/-- A fixed-point word decodes to its signed integer value divided by the scale.
At scale zero the value is the real division junk value zero; accuracy requires positive scale. -/
noncomputable def fixedPointDecode (scale : ℕ) {limit : ℕ} (w : FixedPoint limit) : ℝ :=
  (w.val : ℝ) / (scale : ℝ)

/-- Store an integer if it lies in the fixed-point carrier; reject an out-of-range integer. -/
def fixedPointPack (limit : ℕ) (m : ℤ) : Option (FixedPoint limit) :=
  if h : |m| ≤ (limit : ℤ) then some ⟨m, h⟩ else none

/-- Round a rational down to the fixed-point grid and reject a rounded out-of-range word. -/
def fixedPointRound (scale limit : ℕ) (a : ℚ) : Option (FixedPoint limit) :=
  fixedPointPack limit ⌊a * (scale : ℚ)⌋

/-- A successful checked integer store retains exactly the supplied integer. -/
theorem val_eq_of_fixedPointPack {limit : ℕ} {m : ℤ} {w : FixedPoint limit}
    (h : fixedPointPack limit m = some w) : w.val = m := by
  unfold fixedPointPack at h
  split_ifs at h
  · cases h
    rfl

/-- Successful rational rounding stores its integer floor on the scaled grid. -/
theorem val_eq_floor_of_fixedPointRound {scale limit : ℕ} {a : ℚ} {w : FixedPoint limit}
    (h : fixedPointRound scale limit a = some w) : w.val = ⌊a * (scale : ℚ)⌋ :=
  val_eq_of_fixedPointPack h

/-- Rounding down on a positive-scale grid has absolute error at most one grid spacing. -/
theorem abs_sub_fixedPointDecode_le_of_fixedPointRound {scale limit : ℕ} {a : ℚ}
    {w : FixedPoint limit}
    (hscale : 0 < scale) (h : fixedPointRound scale limit a = some w) :
    |(a : ℝ) - fixedPointDecode scale w| ≤ 1 / (scale : ℝ) := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hlo : (⌊a * (scale : ℚ)⌋ : ℝ) ≤ (a : ℝ) * scale := by
    exact_mod_cast (Int.floor_le (a * (scale : ℚ)))
  have hhi : (a : ℝ) * scale < (⌊a * (scale : ℚ)⌋ : ℝ) + 1 := by
    exact_mod_cast (Int.lt_floor_add_one (a * (scale : ℚ)))
  rw [fixedPointDecode, val_eq_floor_of_fixedPointRound h]
  have hnonneg : 0 ≤ (a : ℝ) - (⌊a * (scale : ℚ)⌋ : ℝ) / scale :=
    sub_nonneg.mpr ((div_le_iff₀ hs).2 hlo)
  rw [abs_of_nonneg hnonneg]
  apply (le_div_iff₀ hs).2
  have heq : ((a : ℝ) - (⌊a * (scale : ℚ)⌋ : ℝ) / scale) * scale =
      (a : ℝ) * scale - (⌊a * (scale : ℚ)⌋ : ℝ) := by
    field_simp
  rw [heq]
  linarith

/-- A checked integer store succeeds when its decoded value is in the fixed-point interval. -/
theorem fixedPointPack_exists_of_abs_div_le {scale limit : ℕ} {m : ℤ}
    (hscale : 0 < scale)
    (h : |(m : ℝ) / (scale : ℝ)| ≤ (limit : ℝ) / (scale : ℝ)) :
    ∃ w, fixedPointPack limit m = some w := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  rw [abs_div, abs_of_pos hs] at h
  have hm : |m| ≤ (limit : ℤ) := by
    exact_mod_cast (div_le_div_iff_of_pos_right hs).mp h
  exact ⟨⟨m, hm⟩, by simp only [fixedPointPack, hm, ↓reduceDIte]⟩

/-- Rounding succeeds for every rational exact value in the closed representable interval. -/
theorem fixedPointRound_exists_of_abs_le {scale limit : ℕ} {a : ℚ}
    (hscale : 0 < scale) (h : |(a : ℝ)| ≤ (limit : ℝ) / (scale : ℝ)) :
    ∃ w, fixedPointRound scale limit a = some w := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hr : |(a : ℝ) * scale| ≤ (limit : ℝ) := by
    rw [abs_mul, abs_of_pos hs]
    exact (le_div_iff₀ hs).mp h
  have hl : -(limit : ℚ) ≤ a * (scale : ℚ) := by
    exact_mod_cast (abs_le.mp hr).1
  have hu : a * (scale : ℚ) ≤ (limit : ℚ) := by
    exact_mod_cast (abs_le.mp hr).2
  have hlo : -(limit : ℤ) ≤ ⌊a * (scale : ℚ)⌋ := Int.le_floor.mpr hl
  have hhi : ⌊a * (scale : ℚ)⌋ ≤ (limit : ℤ) := by
    exact_mod_cast (Int.floor_le (a * (scale : ℚ))).trans hu
  have hm : |⌊a * (scale : ℚ)⌋| ≤ (limit : ℤ) := abs_le.mpr ⟨hlo, hhi⟩
  exact ⟨⟨_, hm⟩, by simp only [fixedPointRound, fixedPointPack, hm, ↓reduceDIte]⟩

/-- Bounded fixed-point scalar arithmetic. Tags share one scale and carrier. Arithmetic returns
`none` on range overflow or division by zero. Square root and bit operations are unsupported. -/
def fixedPointSem {P : Type} (scale limit : ℕ) : ScalarSem P (FixedPoint limit) where
  lit _ q := fixedPointRound scale limit q
  bin _ op x y :=
    let a : ℚ := (x.val : ℚ) / scale
    let b : ℚ := (y.val : ℚ) / scale
    match op with
    | .add => fixedPointPack limit (x.val + y.val)
    | .sub => fixedPointPack limit (x.val - y.val)
    | .mul => fixedPointRound scale limit (a * b)
    | .div => if y.val = 0 then none else fixedPointRound scale limit (a / b)
    | _ => none
  un _ op x := match op with
    | .neg => some ⟨-x.val, by simpa only [abs_neg] using x.property⟩
    | .conj | .re => some x
    | _ => none
  cmp _ op x y := some <| match op with
    | .eq => decide (x.val = y.val)
    | .lt => decide (x.val < y.val)
    | .le => decide (x.val ≤ y.val)
  convert _ _ x := some x

/-- Bounded fixed-point arithmetic satisfies the existing arithmetic contract with zero relative
allowance and absolute allowance $1/s$ at positive scale $s$. Success is guaranteed for exact
results of magnitude at most $\mathit{limit}/s$, with a nonzero divisor for division. No native
fixed-width execution cost is asserted. -/
theorem isArithErrSem_fixedPointSem {P : Type} (scale limit : ℕ) (hscale : 0 < scale) :
    IsArithErrSem (fun _ _ => AbsRelErr 0 (1 / (scale : ℝ)))
      (fun _ => fixedPointDecode scale)
      (fun _ a => |a| ≤ (limit : ℝ) / (scale : ℝ))
      (fixedPointSem (P := P) scale limit) := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hη : 0 ≤ 1 / (scale : ℝ) := le_of_lt (one_div_pos.mpr hs)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p op x y z hop hrun
    cases op <;> simp only [BinOp.IsArith] at hop
    case add =>
      have hz := val_eq_of_fixedPointPack hrun
      simpa only [AbsRelErr, BinOp.realOp, fixedPointDecode, hz, Int.cast_add, add_div,
        sub_self, abs_zero, zero_mul, zero_add] using hη
    case sub =>
      have hz := val_eq_of_fixedPointPack hrun
      simpa only [AbsRelErr, BinOp.realOp, fixedPointDecode, hz, Int.cast_sub, sub_div,
        sub_self, abs_zero, zero_mul, zero_add] using hη
    case mul =>
      have herr := abs_sub_fixedPointDecode_le_of_fixedPointRound hscale hrun
      simpa only [AbsRelErr, zero_mul, zero_add, BinOp.realOp, fixedPointDecode, Rat.cast_mul,
        Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using herr
    case div =>
      by_cases hy : y.val = 0
      · simp only [fixedPointSem, hy, ↓reduceIte] at hrun
        cases hrun
      · have hr : fixedPointRound scale limit
            (((x.val : ℚ) / scale) / ((y.val : ℚ) / scale)) = some z := by
          simpa only [fixedPointSem, hy, ↓reduceIte] using hrun
        have herr := abs_sub_fixedPointDecode_le_of_fixedPointRound hscale hr
        simpa only [AbsRelErr, zero_mul, zero_add, BinOp.realOp, fixedPointDecode,
          Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using herr
  · intro p op x y hop hdiv hsafe
    cases op <;> simp only [BinOp.IsArith] at hop
    case add =>
      apply fixedPointPack_exists_of_abs_div_le hscale
      simpa only [BinOp.realOp, fixedPointDecode, Int.cast_add, add_div] using hsafe
    case sub =>
      apply fixedPointPack_exists_of_abs_div_le hscale
      simpa only [BinOp.realOp, fixedPointDecode, Int.cast_sub, sub_div] using hsafe
    case mul =>
      apply fixedPointRound_exists_of_abs_le hscale
      simpa only [BinOp.realOp, fixedPointDecode, Rat.cast_mul, Rat.cast_div,
        Rat.cast_intCast, Rat.cast_natCast] using hsafe
    case div =>
      have hy : y.val ≠ 0 := by
        intro hy
        apply hdiv rfl
        simp only [fixedPointDecode, hy, Int.cast_zero, zero_div]
      change ∃ z, (if y.val = 0 then none else fixedPointRound scale limit
        (((x.val : ℚ) / scale) / ((y.val : ℚ) / scale))) = some z
      rw [if_neg hy]
      apply fixedPointRound_exists_of_abs_le hscale
      simpa only [BinOp.realOp, fixedPointDecode, Rat.cast_div, Rat.cast_intCast,
        Rat.cast_natCast] using hsafe
  · intro p
    refine ⟨⟨0, by simp only [abs_zero, Int.natCast_nonneg]⟩, ?_, ?_⟩
    · simp only [fixedPointSem, fixedPointRound, zero_mul, Int.floor_zero,
        fixedPointPack, abs_zero, Int.natCast_nonneg, ↓reduceDIte]
    · simp only [fixedPointDecode, Int.cast_zero, zero_div]
  · intro p x
    refine ⟨⟨-x.val, by simpa only [abs_neg] using x.property⟩, rfl, ?_⟩
    simp only [fixedPointDecode, Int.cast_neg, neg_div]
  · intro p x
    exact ⟨x, rfl, rfl⟩

/-- Adding a word that decodes to zero preserves the decoded value exactly on success. -/
theorem addsZeroExactly_fixedPointSem {P : Type} (scale limit : ℕ) (hscale : 0 < scale) :
    AddsZeroExactly (fun _ => fixedPointDecode scale)
      (fixedPointSem (P := P) scale limit) := by
  intro p x y z hrun hx
  have hs : (scale : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hscale)
  have hxzero : x.val = 0 := by
    have hxreal : (x.val : ℝ) = 0 := by
      simpa only [fixedPointDecode, div_eq_zero_iff, hs, or_false] using hx
    exact_mod_cast hxreal
  have hz := val_eq_of_fixedPointPack hrun
  simp only [hxzero, zero_add] at hz
  simp only [fixedPointDecode, hz]

end NLAlib.Computation
