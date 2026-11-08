/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BinaryFloat
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finite.Prod
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Bounded binary floating-point arithmetic

The carrier consists of the real values represented by a binary format. Arithmetic rounds
using the format's variable normal spacing and uniform subnormal spacing. Exact results
outside the closed finite range are rejected before rounding; this conservative overflow
policy is explicit. The integer selector may use any nearest tie policy.

This is a mathematical finite-format interpretation of the existing programs. It does not
identify a ties-up selector with native IEEE ties-to-even, or claim a native runtime bound.
Representation, numerical accuracy and operation costs remain separate certificates.

## Main results

* `NLAlib.Computation.isArithErrSem_binaryFloatSem`: mixed error and range-success certificate.
* `NLAlib.Computation.isFloorRelErrSem_binaryFloatSem`: the floor model with success in the
  finite range.
* `NLAlib.Computation.addsZeroExactly_binaryFloatSem`: exact zero addition.
* `NLAlib.Computation.mulShrinks_binaryFloatSem`: multiplication by a factor of modulus at most
  one does not enlarge.
* `NLAlib.Computation.absRelErr_round`: a concrete nearest-integer selector certificate.
* `NLAlib.Computation.isExactIntLit_binaryFloatSem`: exact integer literals of a bounded binary
  format.
-/

@[expose] public section

namespace NLAlib.Computation

/-- The real values represented by a bounded binary format, including subnormal values.
This mathematical carrier has no separate signed zeros or nonfinite sentinel values. -/
abbrev BinaryFloat (fmt : Float.Model.Format) := {x : ℝ // IsBinaryRep fmt x}

/-- A bounded binary format has finitely many represented real values. This is a
representation theorem, independently of a native implementation or arithmetic cost. -/
theorem finite_binaryFloat (fmt : Float.Model.Format) : Finite (BinaryFloat fmt) := by
  have hfinite := ((Set.finite_Ioo (-(2 ^ fmt.mantissaBits : ℤ))
    (2 ^ fmt.mantissaBits)).prod (Set.finite_Icc fmt.minExponent
      ((2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
        fmt.mantissaBitsWithoutImplicit))).image
    (fun me : ℤ × ℤ => (me.1 : ℝ) * (2 : ℝ) ^ me.2)
  apply Set.Finite.to_subtype (hfinite.subset ?_)
  intro x hx
  obtain ⟨m, e, hm, hmin, hmax, hx⟩ := hx
  exact ⟨(m, e), ⟨abs_lt.mp hm, ⟨hmin, hmax⟩⟩, hx.symm⟩

/-- Round an in-range real value to the bounded binary format; reject an exact result
outside its finite interval. The represented output uses the supplied nearest tie policy. -/
noncomputable def binaryFloatQuantize (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ)
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (a : ℝ) : Option (BinaryFloat fmt) := by
  classical
  exact if h : |a| ≤ fmt.maxFinite then
    some ⟨binaryFloatRound fmt r a, isBinaryRep_binaryFloatRound fmt he hr h⟩
  else none

/-- Successful quantization returns the actual rounded input value. -/
theorem val_eq_binaryFloatRound_of_binaryFloatQuantize
    {fmt : Float.Model.Format} {he : 2 ≤ fmt.exponentBits} {r : ℝ → ℤ}
    {hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)} {a : ℝ} {w : BinaryFloat fmt}
    (h : binaryFloatQuantize fmt he r hr a = some w) : w.val = binaryFloatRound fmt r a := by
  unfold binaryFloatQuantize at h
  split_ifs at h
  · cases h
    rfl

/-- Every exact input in the finite interval can be rounded successfully. -/
theorem exists_binaryFloatQuantize_eq_some_of_abs_le (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ)
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) {a : ℝ}
    (ha : |a| ≤ fmt.maxFinite) : ∃ w, binaryFloatQuantize fmt he r hr a = some w := by
  exact ⟨⟨binaryFloatRound fmt r a, isBinaryRep_binaryFloatRound fmt he hr ha⟩,
    by simp only [binaryFloatQuantize, ha, ↓reduceDIte]⟩

/-- Bounded binary arithmetic with gradual underflow and checked exact-result range.
Negation and real conjugation are exact. Division rejects zero; the square root rejects a
negative argument (no clamping at zero) and rounds the exact root otherwise; word operations
are unsupported. Tags share one format. -/
noncomputable def binaryFloatSem {P : Type} (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ)
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) : ScalarSem P (BinaryFloat fmt) := by
  classical
  exact
    { lit := fun _ q => binaryFloatQuantize fmt he r hr (q : ℝ)
      bin := fun _ op x y => match op with
        | .add => binaryFloatQuantize fmt he r hr (x.val + y.val)
        | .sub => binaryFloatQuantize fmt he r hr (x.val - y.val)
        | .mul => binaryFloatQuantize fmt he r hr (x.val * y.val)
        | .div => if y.val = 0 then none else binaryFloatQuantize fmt he r hr (x.val / y.val)
        | _ => none
      un := fun _ op x => match op with
        | .neg => some ⟨-x.val, x.property.neg⟩
        | .conj | .re => some x
        | .sqrt => if 0 ≤ x.val then binaryFloatQuantize fmt he r hr √x.val else none
        | _ => none
      cmp := fun _ op x y => some <| match op with
        | .eq => decide (x.val = y.val)
        | .lt => decide (x.val < y.val)
        | .le => decide (x.val ≤ y.val)
      convert := fun _ _ x => some x
      toNat := fun _ x => if 0 ≤ x.val then some ⌊x.val⌋₊ else none }

/-- Bounded binary arithmetic satisfies the existing arithmetic interface with relative
allowance $2^{-p}$ and absolute allowance $2^{e_{\min}}/2$. Every exact result in the
closed finite interval succeeds, with nonzero divisors for division. Normal and subnormal
rounding, as well as the finite upper range, are part of the implemented interpretation.
This theorem is independent of the nearest tie policy. [Higham2002, §2.2]. -/
theorem isArithErrSem_binaryFloatSem {P : Type} (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ)
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) :
    IsArithErrSem
      (fun _ _ => AbsRelErr ((2 : ℝ)⁻¹ ^ fmt.mantissaBits) ((2 : ℝ) ^ fmt.minExponent / 2))
      (fun (_ : P) (x : BinaryFloat fmt) => x.val)
      (fun _ a => |a| ≤ fmt.maxFinite) (binaryFloatSem fmt he r hr) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p op x y z hop hrun
    cases op <;> simp only [BinOp.IsArith] at hop
    case add =>
      have hz := val_eq_binaryFloatRound_of_binaryFloatQuantize (he := he) (hr := hr) hrun
      rw [BinOp.realOp, hz]
      exact absRelErr_binaryFloatRound fmt hr _
    case sub =>
      have hz := val_eq_binaryFloatRound_of_binaryFloatQuantize (he := he) (hr := hr) hrun
      rw [BinOp.realOp, hz]
      exact absRelErr_binaryFloatRound fmt hr _
    case mul =>
      have hz := val_eq_binaryFloatRound_of_binaryFloatQuantize (he := he) (hr := hr) hrun
      rw [BinOp.realOp, hz]
      exact absRelErr_binaryFloatRound fmt hr _
    case div =>
      by_cases hy : y.val = 0
      · simp only [binaryFloatSem, hy, ↓reduceIte] at hrun
        cases hrun
      · have hq : binaryFloatQuantize fmt he r hr (x.val / y.val) = some z := by
          simpa only [binaryFloatSem, hy, ↓reduceIte] using hrun
        rw [BinOp.realOp, val_eq_binaryFloatRound_of_binaryFloatQuantize (he := he) (hr := hr) hq]
        exact absRelErr_binaryFloatRound fmt hr _
  · intro p op x y hop hdiv hsafe
    cases op <;> simp only [BinOp.IsArith] at hop
    case add => exact exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr hsafe
    case sub => exact exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr hsafe
    case mul => exact exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr hsafe
    case div =>
      have hy := hdiv rfl
      change ∃ z, (if y.val = 0 then none else
        binaryFloatQuantize fmt he r hr (x.val / y.val)) = some z
      rw [if_neg hy]
      exact exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr hsafe
  · intro p
    have hsafe : |(0 : ℝ)| ≤ fmt.maxFinite := by
      simpa only [abs_zero] using (Float.Model.Format.maxFinite_pos fmt).le
    obtain ⟨w, hw⟩ := exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr hsafe
    refine ⟨w, ?_, ?_⟩
    · simpa only [binaryFloatSem, Rat.cast_zero] using hw
    · rw [val_eq_binaryFloatRound_of_binaryFloatQuantize (he := he) (hr := hr) hw,
        binaryFloatRound_zero fmt hr]
  · intro p x
    exact ⟨⟨-x.val, x.property.neg⟩, rfl, rfl⟩
  · intro p x
    exact ⟨x, rfl, rfl⟩

/-- Successful quantization errs by at most $2^{-p}\max(\lvert a\rvert, 2^{e_{\min} + p - 1})$. -/
private theorem abs_sub_val_le_of_binaryFloatQuantize {fmt : Float.Model.Format}
    {he : 2 ≤ fmt.exponentBits} {r : ℝ → ℤ} {hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)} {a : ℝ}
    {w : BinaryFloat fmt} (h : binaryFloatQuantize fmt he r hr a = some w) :
    |a - w.val| ≤ (2 : ℝ)⁻¹ ^ fmt.mantissaBits *
      max |a| ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) := by
  rw [val_eq_binaryFloatRound_of_binaryFloatQuantize h]
  exact abs_sub_binaryFloatRound_le fmt hr a

/-- **Bounded binary arithmetic meets the floor model**: the bounded binary semantics
`NLAlib.Computation.binaryFloatSem fmt he r hr`, decoding a word to its value, meets
`NLAlib.Computation.IsFloorRelErrSem` at unit roundoff $2^{-p}$ ($p$ the precision of `fmt`,
`fmt.mantissaBits`), floor $2^{e_{\min} + p - 1}$ (the smallest normal number, $e_{\min}$ the
exponent of the subnormal spacing, `fmt.minExponent`) and range condition
$\lvert a\rvert \le \Omega$, $\Omega$ the largest finite number (`fmt.maxFinite`): arithmetic,
literals and the square root round the exact result to within
$2^{-p}\max(\lvert a\rvert, 2^{e_{\min} + p - 1})$ and succeed exactly when it is in range (with
a nonzero divisor, and a nonnegative argument for the square root); negation, conjugation, the
real part, comparisons and conversions are exact. The constants are those of the format: a tie
in the normal range errs by $2^{-p}$ relative, a tie in the subnormal range by half the subnormal
spacing $2^{e_{\min}}/2$. This theorem is independent of the nearest tie policy. [Higham2002,
§2.2], with gradual underflow as a floor. -/
theorem isFloorRelErrSem_binaryFloatSem {P : Type} (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) :
    IsFloorRelErrSem (fun _ => (2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      (fun _ => (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1))
      (fun (_ : P) (x : BinaryFloat fmt) => x.val)
      (fun _ a => |a| ≤ fmt.maxFinite) (binaryFloatSem fmt he r hr) where
  bin_err p op x y z hop hrun := by
    cases op <;> simp only [BinOp.IsArith] at hop
    case add =>
      exact abs_sub_val_le_of_binaryFloatQuantize (he := he) (hr := hr) (a := x.val + y.val) hrun
    case sub =>
      exact abs_sub_val_le_of_binaryFloatQuantize (he := he) (hr := hr) (a := x.val - y.val) hrun
    case mul =>
      exact abs_sub_val_le_of_binaryFloatQuantize (he := he) (hr := hr) (a := x.val * y.val) hrun
    case div =>
      by_cases hy : y.val = 0
      · simp only [binaryFloatSem, hy, ↓reduceIte] at hrun
        cases hrun
      · exact abs_sub_val_le_of_binaryFloatQuantize (he := he) (hr := hr) (a := x.val / y.val)
          (by simpa only [binaryFloatSem, hy, ↓reduceIte] using hrun)
  bin_ok := (isArithErrSem_binaryFloatSem fmt he r hr).bin_ok
  lit_err _ _ _ h := abs_sub_val_le_of_binaryFloatQuantize (he := he) (hr := hr) h
  lit_ok _ _ h := exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr h
  neg _ x := ⟨⟨-x.val, x.property.neg⟩, rfl, rfl⟩
  conj _ x := ⟨x, rfl, rfl⟩
  re _ x := ⟨x, rfl, rfl⟩
  sqrt_err p x z h := by
    by_cases hx : 0 ≤ x.val
    · have h' := abs_sub_val_le_of_binaryFloatQuantize (he := he) (hr := hr) (a := √x.val)
        (by simpa only [binaryFloatSem, hx, ↓reduceIte] using h)
      rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h'
    · simp only [binaryFloatSem, hx, ↓reduceIte] at h
      cases h
  sqrt_ok p x hx hsafe := by
    change ∃ z, (if 0 ≤ x.val then binaryFloatQuantize fmt he r hr √x.val else none) = some z
    rw [if_pos hx]
    exact exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr hsafe
  cmp_eq _ _ _ := rfl
  cmp_lt _ _ _ := rfl
  cmp_le _ _ _ := rfl
  convert_err p q x z h := by
    cases Option.some.inj h
    rw [sub_self, abs_zero]
    positivity
  convert_ok _ _ x _ := ⟨x, rfl⟩

/-- Bounded binary multiplication by a factor of modulus at most one does not enlarge: the
bounded binary semantics `NLAlib.Computation.binaryFloatSem fmt he r hr`, decoding a word to its
value, meets `NLAlib.Computation.MulShrinks`: if $\lvert y\rvert \le 1$, the rounding of $xy$
has magnitude at most $\lvert x\rvert$, since $x$ is represented and rounding never passes a
represented value of larger magnitude. This theorem is independent of the nearest tie policy. No
printed source. -/
theorem mulShrinks_binaryFloatSem {P : Type} (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) :
    MulShrinks (fun (_ : P) (x : BinaryFloat fmt) => x.val) (binaryFloatSem fmt he r hr) := by
  intro p x y z h hy
  change |z.val| ≤ |x.val|
  rw [val_eq_binaryFloatRound_of_binaryFloatQuantize (he := he) (hr := hr) h]
  refine abs_binaryFloatRound_le_of_abs_le fmt hr x.property ?_
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hy

/-- Adding a represented zero is exact because rounding fixes every represented value. -/
theorem addsZeroExactly_binaryFloatSem {P : Type} (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ)
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) :
    AddsZeroExactly (fun (_ : P) (x : BinaryFloat fmt) => x.val)
      (binaryFloatSem fmt he r hr) := by
  intro p x y z hrun hx
  change x.val = 0 at hx
  change z.val = y.val
  have hz := val_eq_binaryFloatRound_of_binaryFloatQuantize (he := he) (hr := hr) hrun
  rw [hx, zero_add, binaryFloatRound_eq_self fmt hr y.property] at hz
  exact hz

/-- Mathlib's integer rounder is a concrete nearest selector. Its ties-up convention is
one admissible policy, independently of IEEE's ties-to-even convention. -/
theorem absRelErr_round (x : ℝ) : AbsRelErr 0 (1 / 2) x (round x : ℝ) := by
  simpa only [AbsRelErr, zero_mul, zero_add] using abs_sub_round x

/-! ### Exact integer literals -/

section ExactIntLit

open Float.Model

/-- A bounded binary format has exact integer literals: if $B < 2^p$, $p$ the precision of
`fmt` (`fmt.mantissaBits`), and the exponent $0$ lies in the range of the format (at least its
minimum exponent and at most its largest significand exponent), then the bounded binary semantics
`NLAlib.Computation.binaryFloatSem fmt he r hr`, decoding a word to its value, meets
`NLAlib.Computation.IsExactIntLit` at $B$: every natural number $k \le B$ is a represented value,
and binary rounding fixes it. No printed source. -/
theorem isExactIntLit_binaryFloatSem {P : Type} (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (B : ℕ)
    (hB : B < 2 ^ fmt.mantissaBits) (hmin : fmt.minExponent ≤ 0)
    (hmax : 0 ≤ (2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
      fmt.mantissaBitsWithoutImplicit) :
    IsExactIntLit (fun _ x => x.val) (binaryFloatSem (P := P) fmt he r hr) B := by
  intro q k hk
  have hrep : IsBinaryRep fmt (k : ℝ) := by
    refine ⟨k, 0, ?_, hmin, hmax, by simp⟩
    simpa [abs_of_nonneg (Int.natCast_nonneg k)] using
      (by exact_mod_cast hk.trans_lt hB : (k : ℤ) < 2 ^ fmt.mantissaBits)
  have hq : binaryFloatQuantize fmt he r hr ((k : ℚ) : ℝ) = some ⟨(k : ℝ), hrep⟩ := by
    rw [Rat.cast_natCast, binaryFloatQuantize, dif_pos hrep.abs_le]
    congr 1
    exact Subtype.ext (binaryFloatRound_eq_self fmt hr hrep)
  exact ⟨_, hq, rfl⟩

/-- Bounded binary arithmetic converts exactly: `NLAlib.Computation.binaryFloatSem`, decoding a
word to its value, meets `NLAlib.Computation.IsExactToNat` (the floor of the value, failing below
zero). No printed source. -/
theorem isExactToNat_binaryFloatSem {P : Type} (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) :
    IsExactToNat (P := P) (fun _ x => x.val) (binaryFloatSem fmt he r hr) :=
  fun _ _ => rfl

/-- A bounded binary format is index exact: if $B < 2^p$, $p$ the precision of `fmt`
(`fmt.mantissaBits`), and the exponent $0$ lies in the range of the format (at least its minimum
exponent and at most its largest significand exponent), then the bounded binary semantics
`NLAlib.Computation.binaryFloatSem fmt he r hr`, decoding a word to its value, meets
`NLAlib.Computation.IsIndexExactSem` at $B$: its integer literals up to $B$ are exact and its
conversion to an index is the floor of the value, failing below zero. No printed source. -/
theorem isIndexExactSem_binaryFloatSem {P : Type} (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (B : ℕ)
    (hB : B < 2 ^ fmt.mantissaBits) (hmin : fmt.minExponent ≤ 0)
    (hmax : 0 ≤ (2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
      fmt.mantissaBitsWithoutImplicit) :
    IsIndexExactSem (fun _ x => x.val) B (binaryFloatSem (P := P) fmt he r hr) :=
  ⟨isExactIntLit_binaryFloatSem fmt he r hr B hB hmin hmax,
    isExactToNat_binaryFloatSem fmt he r hr⟩

end ExactIntLit

end NLAlib.Computation
