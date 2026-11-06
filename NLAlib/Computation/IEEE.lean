/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import NLAlib.Computation.BinaryFloat
public import NLAlib.ForMathlib.Data.Float.Operations
public import NLAlib.ForMathlib.Data.Float.Literals

/-!
# Certified finite binary64 arithmetic

The finite-word endpoint uses actual Lean `Float` operations through core's logical model.
The inherited arithmetic interface separates successful-operation accuracy from input-based
range success. Gradual underflow is retained as an absolute error allowance; overflow and
invalid operations are rejected by checked execution. No private numerical package is imported.

The format-generic core-model accuracy proofs are adapted from the supplied NumLean archive;
source paths, archive hash and licensing status are recorded in
`docs/design/Finite-Precision-Arithmetic.md`. Native runtime replacements remain trusted to
implement Lean's model. Counts and physical kernel costs are separate certificates.

## Main results

* `NLAlib.Computation.isArithErrSem_finiteFloatSem`: mixed-error accuracy and range success.
* `NLAlib.Computation.addsZeroExactly_finiteFloatSem`: exact zero addition for kernel accumulation.
-/

@[expose] public section

namespace NLAlib.Computation

open Float.Model Float.Model.UnpackedFloat

private local instance : Fact (2 ≤ Format.binary64.exponentBits) := ⟨by decide⟩

private theorem native_canonical (x : Float) : IsCanonical .binary64 x.toModel.unpack :=
  unpack_isCanonical .binary64 x.toModel.toBits.toBitVec

/-- The checked Float decoding agrees with the real value of core's unpacked model. -/
theorem floatDecode_eq_toReal (x : Float) : floatDecode x = x.toModel.unpack.toReal := by
  unfold floatDecode
  cases x.toModel.unpack with
  | finite s m e hm => cases s <;> simp only [toReal, Sign.toReal, neg_mul, one_mul]
  | _ => rfl

private theorem native_pack_value {x : Float} {r : UnpackedFloat}
    (hr : IsCanonical .binary64 r)
    (hx : x.toModel.unpack = UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 r))
    (hf : x.isFinite = true) : r.IsFinite ∧ floatDecode x = r.toReal := by
  have hf' : (UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 r)).IsFinite := by
    rw [← hx]
    exact hf
  have he := unpack_pack_of_isFinite hr hf'
  rw [he] at hf'
  exact ⟨hf', by rw [floatDecode_eq_toReal, hx, he]⟩

private theorem float_add_error (x y : Float) (hf : (x + y).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) 0
      (floatDecode x + floatDecode y) (floatDecode (x + y)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x + y)
    (add_isCanonical _ _ (native_canonical x) (native_canonical y)) rfl hf
  have he := abs_toReal_add_sub_le _ _ (native_canonical x) (native_canonical y) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, add_zero, abs_sub_comm] using he

private theorem float_sub_error (x y : Float) (hf : (x - y).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) 0
      (floatDecode x - floatDecode y) (floatDecode (x - y)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x - y)
    (sub_isCanonical _ _ (native_canonical x) (native_canonical y)) rfl hf
  have he := abs_toReal_sub_sub_le _ _ (native_canonical x) (native_canonical y) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, add_zero, abs_sub_comm] using he

private theorem float_mul_error (x y : Float) (hf : (x * y).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) (Format.binary64.underflowBound)
      (floatDecode x * floatDecode y) (floatDecode (x * y)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x * y)
    (mul_isCanonical _ _ (native_canonical x) (native_canonical y)) rfl hf
  have he := abs_toReal_mul_sub_le _ _ (native_canonical x) (native_canonical y) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, abs_sub_comm] using he

private theorem float_div_error (x y : FiniteFloat) (hf : (x.val / y.val).isFinite = true) :
    AbsRelErr (Format.binary64.unitRoundoff) (Format.binary64.underflowBound)
      (floatDecode x.val / floatDecode y.val) (floatDecode (x.val / y.val)) := by
  obtain ⟨hr, hv⟩ := native_pack_value (x := x.val / y.val)
    (div_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)) rfl hf
  have he := abs_toReal_div_sub_le _ _ (native_canonical x.val) (native_canonical y.val)
    x.property y.property hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, ← hv] at he
  simpa only [AbsRelErr, abs_sub_comm] using he

open Float.Model.BinaryRounding

private theorem native_isFinite_of_nearest {r : UnpackedFloat} {a : ℝ}
    (hc : IsCanonical .binary64 r) (hf : r.IsFinite)
    (hn : IsNearestFloat Format.binary64.mantissaBits Format.binary64.minExponent a r.toReal)
    (hs : |a| ≤ Format.binary64.maxFinite) :
    (Float.ofModel (Float.Model.pack r)).isFinite = true := by
  have hm : 0 ≤ Format.binary64.maxFinite := by
    unfold Format.maxFinite
    exact mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num))) (by positivity)
  have hb := hn.abs_le_of_abs_le (Format.isBinaryFloat_maxFinite .binary64)
    (by rwa [abs_of_nonneg hm])
  rw [abs_of_nonneg hm] at hb
  have he := unpack_pack_of_abs_toReal_le hc hf hb
  change (UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 r)).isFinite = true
  rw [he]
  exact hf

private theorem float_add_isFinite (x y : FiniteFloat)
    (hs : |floatDecode x.val + floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val + y.val).isFinite = true := by
  have hc := add_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  have hf := isFinite_add_of_isFinite (spec := .binary64) _ _ x.property y.property
  have hn := isNearestFloat_toReal_add _ _ (native_canonical x.val) (native_canonical y.val) hf
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

private theorem float_sub_isFinite (x y : FiniteFloat)
    (hs : |floatDecode x.val - floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val - y.val).isFinite = true := by
  have hc := sub_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  have hf := isFinite_sub_of_isFinite (spec := .binary64) _ _ x.property y.property
  have hn := isNearestFloat_toReal_sub _ _ (native_canonical x.val) (native_canonical y.val) hf
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

private theorem float_mul_isFinite (x y : FiniteFloat)
    (hs : |floatDecode x.val * floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val * y.val).isFinite = true := by
  have hc := mul_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  have hf := isFinite_mul_of_isFinite (spec := .binary64) _ _ x.property y.property
  have hn := isNearestFloat_toReal_mul _ _ (native_canonical x.val) (native_canonical y.val) hf
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

private theorem div_finite_nearest
    (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (s₁ s₂ : Sign) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    IsNearestFloat Format.binary64.mantissaBits Format.binary64.minExponent
      ((UnpackedFloat.finite s₁ m₁ e₁ hm₁).toReal /
        (UnpackedFloat.finite s₂ m₂ e₂ hm₂).toReal)
      (UnpackedFloat.div .binary64 (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂)).toReal := by
  obtain ⟨w, hw, hwv, he⟩ := exists_approximates_divCore (spec := .binary64)
    m₁ e₁ m₂ e₂ hm₁ hm₂
  have hn := isNearestFloat_toReal_roundWithAccuracy .binary64 (s₁ / s₂) _ _ _ w hw he
  rw [hwv] at hn
  have hv : toReal (.finite s₁ m₁ e₁ hm₁) / toReal (.finite s₂ m₂ e₂ hm₂)
      = (s₁ / s₂).toReal * ((m₁ * 2 ^ e₁) / (m₂ * 2 ^ e₂)) := by
    simp only [toReal, Sign.toReal_div]
    field_simp
    cases s₂ <;> cases s₁ <;> simp [Sign.toReal]
  rw [hv]
  exact hn

private theorem div_finite_nearest_of_finite (x y : UnpackedFloat)
    (hx : x.IsFinite) (hy : y.IsFinite) (hy0 : y.toReal ≠ 0) :
    (UnpackedFloat.div .binary64 x y).IsFinite ∧
      IsNearestFloat Format.binary64.mantissaBits Format.binary64.minExponent
        (x.toReal / y.toReal) (UnpackedFloat.div .binary64 x y).toReal := by
  cases x <;> cases y <;>
    first
    | (simp only [UnpackedFloat.IsFinite, UnpackedFloat.isFinite, Bool.false_eq_true] at hx; done)
    | (simp only [UnpackedFloat.IsFinite, UnpackedFloat.isFinite, Bool.false_eq_true] at hy; done)
    | (simp only [toReal, ne_eq, not_true_eq_false] at hy0; done)
    | skip
  case zero.finite s₁ s₂ m₂ e₂ hm₂ =>
    simp only [UnpackedFloat.div, UnpackedFloat.IsFinite, UnpackedFloat.isFinite, toReal,
      zero_div, true_and]
    exact isNearestFloat_self isBinaryFloat_zero
  case finite.finite s₁ m₁ e₁ hm₁ s₂ m₂ e₂ hm₂ =>
    exact ⟨isFinite_roundWithAccuracy _ _ _ _ _, div_finite_nearest m₁ m₂ e₁ e₂ s₁ s₂ hm₁ hm₂⟩

private theorem float_div_isFinite (x y : FiniteFloat) (hy : floatDecode y.val ≠ 0)
    (hs : |floatDecode x.val / floatDecode y.val| ≤ Format.binary64.maxFinite) :
    (x.val / y.val).isFinite = true := by
  have hc := div_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)
  obtain ⟨hf, hn⟩ := div_finite_nearest_of_finite x.val.toModel.unpack y.val.toModel.unpack
    x.property y.property (by rwa [← floatDecode_eq_toReal])
  apply native_isFinite_of_nearest hc hf hn
  rwa [← floatDecode_eq_toReal, ← floatDecode_eq_toReal]

private theorem finiteFloatSem_bin_error (b : BinOp) (x y z : FiniteFloat)
    (hb : b.IsArith) (h : finiteFloatSem.bin () b x y = some z) :
    AbsRelErr Format.binary64.unitRoundoff Format.binary64.underflowBound
      (b.realOp (floatDecode x.val) (floatDecode y.val)) (floatDecode z.val) := by
  have hr := map_finiteFloatSem_bin b x y
  rw [h, Option.map_some] at hr
  obtain ⟨_, _, _, hm⟩ := (bin_checkedFloatSem_eq_some_iff b x.val y.val z.val).mp hr.symm
  cases b <;> simp only [BinOp.IsArith] at hb
  case add =>
    have heq : z.val = x.val + y.val := congrArg Float.ofModel hm
    have he := float_add_error x.val y.val (heq ▸ z.property)
    simpa only [BinOp.realOp, heq] using
      he.mono le_rfl (Format.underflowBound_nonneg .binary64)
  case sub =>
    have heq : z.val = x.val - y.val := congrArg Float.ofModel hm
    have he := float_sub_error x.val y.val (heq ▸ z.property)
    simpa only [BinOp.realOp, heq] using
      he.mono le_rfl (Format.underflowBound_nonneg .binary64)
  case mul =>
    have heq : z.val = x.val * y.val := congrArg Float.ofModel hm
    have he := float_mul_error x.val y.val (heq ▸ z.property)
    simpa only [BinOp.realOp, heq] using he
  case div =>
    have heq : z.val = x.val / y.val := congrArg Float.ofModel hm
    have he := float_div_error x y (heq ▸ z.property)
    simpa only [BinOp.realOp, heq] using he

private theorem finiteFloatSem_bin_exists_of_raw {b : BinOp} {x y : FiniteFloat} {z : Float}
    (h : checkedFloatSem.bin () b x.val y.val = some z) :
    ∃ w, finiteFloatSem.bin () b x y = some w := by
  have hr := map_finiteFloatSem_bin b x y
  rw [h] at hr
  obtain ⟨w, hw, _⟩ := Option.map_eq_some_iff.mp hr
  exact ⟨w, hw⟩

private theorem finiteFloatSem_bin_exists (b : BinOp) (x y : FiniteFloat)
    (hb : b.IsArith) (hdiv : b = .div → floatDecode y.val ≠ 0)
    (hs : |b.realOp (floatDecode x.val) (floatDecode y.val)| ≤ Format.binary64.maxFinite) :
    ∃ z, finiteFloatSem.bin () b x y = some z := by
  cases b <;> simp only [BinOp.IsArith] at hb
  case add =>
    have hf := float_add_isFinite x y hs
    apply finiteFloatSem_bin_exists_of_raw (z := x.val + y.val)
    simp only [checkedFloatSem, x.property, y.property, Bool.and_self, ↓reduceIte,
      checkedFloat, hf]
  case sub =>
    have hf := float_sub_isFinite x y hs
    apply finiteFloatSem_bin_exists_of_raw (z := x.val - y.val)
    simp only [checkedFloatSem, x.property, y.property, Bool.and_self, ↓reduceIte,
      checkedFloat, hf]
  case mul =>
    have hf := float_mul_isFinite x y hs
    apply finiteFloatSem_bin_exists_of_raw (z := x.val * y.val)
    simp only [checkedFloatSem, x.property, y.property, Bool.and_self, ↓reduceIte,
      checkedFloat, hf]
  case div =>
    have hf := float_div_isFinite x y (hdiv rfl) hs
    apply finiteFloatSem_bin_exists_of_raw (z := x.val / y.val)
    simp only [checkedFloatSem, x.property, y.property, Bool.and_self, ↓reduceIte,
      checkedFloat, hf]




private theorem native_neg_exact (x : FiniteFloat) :
    (-x.val).isFinite = true ∧ floatDecode (-x.val) = -floatDecode x.val := by
  have hb : |floatDecode x.val| ≤ Format.binary64.maxFinite := by
    exact (isBinaryRep_floatDecode x.val).abs_le
  have hc := neg_isCanonical x.val.toModel.unpack (native_canonical x.val)
  have hf : x.val.toModel.unpack.neg.IsFinite :=
    (isFinite_neg x.val.toModel.unpack).mpr x.property
  have hv : x.val.toModel.unpack.neg.toReal = -floatDecode x.val := by
    rw [toReal_neg, ← floatDecode_eq_toReal]
  have hn := isNearestFloat_self (isBinaryFloat_toReal hc)
  have hout : (-x.val).isFinite = true :=
    native_isFinite_of_nearest hc hf hn (by rw [hv, abs_neg]; exact hb)
  have hvalue := native_pack_value (x := -x.val) hc rfl hout
  exact ⟨hout, hvalue.2.trans hv⟩

private theorem finiteFloatSem_neg (x : FiniteFloat) :
    ∃ z, finiteFloatSem.un () .neg x = some z ∧
      floatDecode z.val = -floatDecode x.val := by
  obtain ⟨hf, hv⟩ := native_neg_exact x
  refine ⟨⟨-x.val, hf⟩, ?_, hv⟩
  apply Option.map_injective Subtype.val_injective
  rw [map_finiteFloatSem_un, Option.map_some]
  exact (un_checkedFloatSem_eq_some_iff .neg x.val (-x.val)).2 ⟨x.property, hf, rfl⟩

private theorem finiteFloatSem_zero :
    ∃ z, finiteFloatSem.lit () 0 = some z ∧ floatDecode z.val = 0 := by
  refine ⟨⟨Float.ofBits 0, rfl⟩, ?_, ?_⟩
  · apply Option.map_injective Subtype.val_injective
    rw [map_finiteFloatSem_lit, Option.map_some]
    simp only [checkedFloatSem, Rat.num_zero, Rat.den_zero, checkedFloat,
      Float.isFinite_ofInt_zero,
      Float.isFinite_ofNat_one, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
      Float.div_ofInt_zero_ofNat_one]
    rfl
  · rfl

private theorem finiteFloatSem_conj (x : FiniteFloat) :
    ∃ z, finiteFloatSem.un () .conj x = some z ∧ floatDecode z.val = floatDecode x.val := by
  refine ⟨x, ?_, rfl⟩
  apply Option.map_injective Subtype.val_injective
  rw [map_finiteFloatSem_un, Option.map_some]
  exact (un_checkedFloatSem_eq_some_iff .conj x.val x.val).2 ⟨x.property, x.property, rfl⟩

/-- Adding a finite binary64 word whose real value is zero preserves the other real value
exactly whenever the checked operation succeeds, including the subnormal range and signed zero.
The assertion concerns decoded values, not equality of signed-zero bit patterns. -/
theorem addsZeroExactly_finiteFloatSem :
    AddsZeroExactly (fun _ (x : FiniteFloat) => floatDecode x.val) finiteFloatSem := by
  intro p x y z hrun hx
  cases p
  change floatDecode x.val = 0 at hx
  have hm := map_finiteFloatSem_bin .add x y
  rw [hrun] at hm
  have hraw : checkedFloatSem.bin () .add x.val y.val = some z.val := hm.symm
  have heq := ((bin_checkedFloatSem_eq_some_iff .add x.val y.val z.val).mp hraw).2.2.2
  have hz : z.val = x.val + y.val := congrArg Float.ofModel heq
  have hf : (x.val + y.val).isFinite = true := by rw [← hz]; exact z.property
  obtain ⟨hr, hv⟩ := native_pack_value (x := x.val + y.val)
    (add_isCanonical _ _ (native_canonical x.val) (native_canonical y.val)) rfl hf
  have hn := isNearestFloat_toReal_add _ _ (native_canonical x.val) (native_canonical y.val) hr
  rw [← floatDecode_eq_toReal, ← floatDecode_eq_toReal, hx, zero_add] at hn
  have hrepr : Float.Model.BinaryRounding.IsBinaryFloat Format.binary64.mantissaBits
      Format.binary64.minExponent (floatDecode y.val) := by
    rw [floatDecode_eq_toReal]
    exact isBinaryFloat_toReal (native_canonical y.val)
  have hfix := hn.eq_of_isBinaryFloat hrepr
  change floatDecode z.val = floatDecode y.val
  rw [hz, hv, hfix]


/-- Finite binary64 arithmetic satisfies the existing scalar arithmetic contract with relative
allowance $2^{-53}$ and absolute underflow allowance $2^{-1075}$. Every exact arithmetic result
within the largest finite magnitude succeeds, with a nonzero divisor for division. The absolute
allowance is conservative for addition and subtraction, which need no underflow term.

This is proved from Lean core's logical `Float.Model`, including bounded exponents and gradual
underflow. It certifies the checked interpreter on finite words, not the correctness or physical
cost of native runtime replacements. Only the zero literal is required by this arithmetic
contract; arbitrary rational-literal conversion is a separate obligation.
[Higham2002, §2.2]. -/
theorem isArithErrSem_finiteFloatSem :
    IsArithErrSem
      (fun _ _ => AbsRelErr Format.binary64.unitRoundoff Format.binary64.underflowBound)
      (fun _ (x : FiniteFloat) => floatDecode x.val)
      (fun _ a => |a| ≤ Format.binary64.maxFinite) finiteFloatSem := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p b x y z hb hrun
    cases p
    exact finiteFloatSem_bin_error b x y z hb hrun
  · intro p b x y hb hdiv hs
    cases p
    exact finiteFloatSem_bin_exists b x y hb hdiv hs
  · intro p
    cases p
    exact finiteFloatSem_zero
  · intro p x
    cases p
    exact finiteFloatSem_neg x
  · intro p x
    cases p
    exact finiteFloatSem_conj x

end NLAlib.Computation
