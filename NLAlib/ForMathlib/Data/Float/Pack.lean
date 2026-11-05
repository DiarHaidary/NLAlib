/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Float.Rounding
public import Init.Data.Float.Model.Float
public import Batteries.Data.Float.Lemmas

/-!
# Packing, unpacking and overflow in the Float model

Upstream candidates for the mathematical API of Lean core's floating-point model.
Adapted from the supplied NumLean archive, `NumLean/Data/Scalars/IEEE/Pack.lean`. The archive's
SHA-256 and licensing status, the earlier Mathlib search and the changes needed for Lean 4.33
are recorded in `docs/design/Finite-Precision-Arithmetic.md`. No NumLean dependency is imported.
General format lemmas state a two-exponent-bit assumption explicitly where needed; core 4.33
also permits one-bit layouts. These results concern logical arithmetic, not native execution cost.

## Main results

* `Float.Model.UnpackedFloat.unpack_isCanonical`.
* `Float.Model.UnpackedFloat.unpack_pack_of_abs_toReal_le`.
* `Float.Model.UnpackedFloat.unpack_pack_unpack`.
-/

@[expose] public section

namespace Float.Model.UnpackedFloat

variable {spec : Format} [Fact (2 ≤ spec.exponentBits)]

/-- Prepending the implicit bit to a mantissa adds `2 ^ n`. -/
theorem toNat_one_append {n : Nat} (m : BitVec n) : (1#1 ++ m).toNat = 2 ^ n + m.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, BitVec.toNat_one, Nat.one_mul,
    ← Nat.mul_one (2 ^ n), Nat.two_pow_add_eq_or_of_lt m.isLt 1]
  decide

private theorem allOnes_ne_zero (spec : Format) [Fact (2 ≤ spec.exponentBits)] :
  (-1#spec.exponentBits) ≠ 0#_ := by
  have := (Fact.out (p := 2 ≤ spec.exponentBits))
  rw [BitVec.neg_one_eq_allOnes]
  intro h
  have := congrArg BitVec.toNat h
  simp at this
  have : 2 ≤ 2 ^ spec.exponentBits := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem unpack_isCanonical (spec : Format) [Fact (2 ≤ spec.exponentBits)] (b : BitVec
  spec.numBits) :
    IsCanonical spec (unpack spec b) := by
  have hmw := spec.hm
  unfold unpack
  simp only
  split
  · split <;> trivial
  · split
    · split
      · trivial
      · -- subnormal
        next h0 hz =>
        refine ⟨?_, ?_, Or.inr ?_⟩
        · rw [h0, Format.minExponent_eq]; simp; linarith
        · have := (unpackMantissa b).isLt
          unfold Format.mantissaBits
          exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
        · rw [h0, Format.minExponent_eq]; simp; ring
    · -- normal
      next h1 h0 =>
      have hE : 1 ≤ (unpackExponent b).toNat := by
        rcases Nat.eq_zero_or_pos (unpackExponent b).toNat with h | h
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
        · exact h
      have hM := (unpackMantissa b).isLt
      have hp : spec.mantissaBits - 1 = spec.mantissaBitsWithoutImplicit := by
        unfold Format.mantissaBits; omega
      have hval := toNat_one_append (unpackMantissa b)
      refine ⟨?_, ?_, Or.inl ?_⟩
      · rw [Format.minExponent_eq]; omega
      · rw [hval]; unfold Format.mantissaBits
        rw [Nat.add_comm 1, pow_succ]; omega
      · rw [hval, hp]; omega

private theorem zero_ne_allOnes (spec : Format) [Fact (2 ≤ spec.exponentBits)] :
  (0#spec.exponentBits) ≠ -1#_ :=
  (allOnes_ne_zero spec).symm

@[simp] theorem unpack_pack_zero (s : Sign) :
    unpack spec (pack spec (.zero s)) = .zero s := by
  have : spec.exponentBits ≠ 0 := by have := (Fact.out (p := 2 ≤ spec.exponentBits)); omega
  simp [unpack, pack, packedZero, unpackSign_packComponents, this]

omit [Fact (2 ≤ spec.exponentBits)] in
@[simp] theorem unpack_pack_infinity (s : Sign) :
    unpack spec (pack spec (.infinity s)) = .infinity s := by
  simp [unpack, pack, packedInfinity, unpackSign_packComponents]

private theorem packedNaN_mantissa_ne_zero (spec : Format) :
    (1#spec.mantissaBitsWithoutImplicit <<< (spec.mantissaBitsWithoutImplicit - 1)) ≠ 0#_ := by
  have hmw := spec.hm
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.one_mod_eq_one.mpr (by
    have : 2 ≤ 2 ^ spec.mantissaBitsWithoutImplicit := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hmw
    omega), Nat.shiftLeft_eq, Nat.one_mul,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))] at this
  simp at this

omit [Fact (2 ≤ spec.exponentBits)] in
@[simp] theorem unpack_pack_nan :
    unpack spec (pack spec .notANumber) = .notANumber := by
  simp [unpack, pack, packedNaN, packedNaN_mantissa_ne_zero]

/-- The biased exponent of a finite float does not overflow. -/
def FitsExponentRange (spec : Format) (e : ℤ) : Prop :=
  (e + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat + 1 < 2 ^ spec.exponentBits

/-- The integers of `p` bits do not overflow iff $p \le e_{\max}+1$; this holds for
  binary16/32/64/128. -/
theorem fitsExponentRange_zero_iff (spec : Format) [Fact (2 ≤ spec.exponentBits)] :
    FitsExponentRange spec 0 ↔ spec.mantissaBits ≤ spec.exponentBias + 1 := by
  have h2 : 2 ^ spec.exponentBits = 2 * 2 ^ (spec.exponentBits - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, spec.exponentBits = k + 1 := by
      refine ⟨spec.exponentBits - 1, ?_⟩
      have := (Fact.out (p := 2 ≤ spec.exponentBits))
      omega
    rw [hk]; simp [pow_succ, mul_comm]
  have h3 : 0 < 2 ^ (spec.exponentBits - 1) := Nat.two_pow_pos _
  unfold FitsExponentRange Format.exponentBias Format.mantissaBits
  rw [h2]
  omega

/-- A float does not overflow exactly when its exponent is below the format's upper limit. -/
theorem fitsExponentRange_iff (spec : Format) [Fact (2 ≤ spec.exponentBits)] (e : ℤ) :
    FitsExponentRange spec e ↔ e ≤ spec.maxExponentBound := by
  unfold FitsExponentRange Format.maxExponentBound
  have := (Fact.out (p := 2 ≤ spec.exponentBits))
  have h4 : 4 ≤ 2 ^ spec.exponentBits := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
  omega

theorem unpack_pack_finite_of_fitsExponentRange {s : Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (hc : IsCanonical spec (.finite s m e hm)) (hno : FitsExponentRange spec e) :
    unpack spec (pack spec (.finite s m e hm)) = .finite s m e hm := by
  obtain ⟨hmin, hmp, hlow⟩ := hc
  have hmw := spec.hm
  have heb := (Fact.out (p := 2 ≤ spec.exponentBits))
  have hpdef : spec.mantissaBits = spec.mantissaBitsWithoutImplicit + 1 := by
    unfold Format.mantissaBits; omega
  rw [Format.minExponent_eq] at hmin hlow
  unfold pack
  simp only
  generalize hbiased : (e + ↑spec.exponentBias + ↑spec.mantissaBitsWithoutImplicit).toNat = biased
  have hb : (biased : ℤ) = e + spec.exponentBias + spec.mantissaBitsWithoutImplicit := by
    rw [← hbiased]; exact Int.toNat_of_nonneg (by omega)
  have hov : ¬ 2 ^ spec.exponentBits ≤ biased + 1 := by
    unfold FitsExponentRange at hno; rw [hbiased] at hno; omega
  simp only [hov, ↓reduceIte]
  have hl := (Nat.log2_eq_iff hm.ne').mp rfl
  have hEpos : 2 ≤ 2 ^ spec.exponentBits := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hN : m.log2 + 1 = spec.mantissaBits
  · simp only [hN, ↓reduceIte]
    -- normal
    have hbt : (BitVec.ofNat spec.exponentBits biased).toNat = biased := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hne1 : BitVec.ofNat spec.exponentBits biased ≠ -1#_ := by
      intro h; have := congrArg BitVec.toNat h
      rw [hbt, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at this; omega
    have hne0 : BitVec.ofNat spec.exponentBits biased ≠ 0#_ := by
      intro h; have := congrArg BitVec.toNat h
      rw [hbt] at this; simp at this; omega
    have hlog : m.log2 = spec.mantissaBitsWithoutImplicit := by rw [hpdef] at hN; omega
    have hm1 : 2 ^ spec.mantissaBitsWithoutImplicit ≤ m := hlog ▸ hl.1
    have hm2 : m < 2 * 2 ^ spec.mantissaBitsWithoutImplicit := by
      have := hl.2; rw [hlog, pow_succ] at this; omega
    have hmant : (1#1 ++ BitVec.ofNat spec.mantissaBitsWithoutImplicit m).toNat = m := by
      rw [toNat_one_append, BitVec.toNat_ofNat]
      have : m % 2 ^ spec.mantissaBitsWithoutImplicit = m - 2 ^ spec.mantissaBitsWithoutImplicit
        := by
        rw [Nat.mod_eq_sub_mod hm1, Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [unpack, unpackExponent_packComponents, unpackMantissa_packComponents,
      unpackSign_packComponents, Sign.ofBitVec_toBitVec, hne1, hne0, ite_false, hmant, hbt]
    congr 1
    omega
  · simp only [hN, ↓reduceIte]
    -- subnormal
    have hsub : m < 2 ^ spec.mantissaBitsWithoutImplicit ∧
        e = 1 - (spec.exponentBias : ℤ) - spec.mantissaBitsWithoutImplicit := by
      rcases hlow with h | h
      · exfalso; apply hN
        have : m.log2 = spec.mantissaBits - 1 := by
          rw [Nat.log2_eq_iff hm.ne']
          exact ⟨h, by rwa [Nat.sub_add_cancel (by omega)]⟩
        omega
      · refine ⟨?_, h⟩
        rcases Nat.lt_or_ge m (2 ^ spec.mantissaBitsWithoutImplicit) with h' | h'
        · exact h'
        · exfalso; apply hN
          have : m.log2 = spec.mantissaBitsWithoutImplicit := by
            rw [Nat.log2_eq_iff hm.ne']; exact ⟨h', by rwa [hpdef] at hmp⟩
          omega
    have hmt : (BitVec.ofNat spec.mantissaBitsWithoutImplicit m).toNat = m := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hsub.1
    have hne0 : BitVec.ofNat spec.mantissaBitsWithoutImplicit m ≠ 0#_ := by
      intro h; have := congrArg BitVec.toNat h; rw [hmt] at this; simp at this; omega
    simp only [unpack, unpackExponent_packComponents, unpackMantissa_packComponents,
      unpackSign_packComponents, Sign.ofBitVec_toBitVec, zero_ne_allOnes, hne0, ite_false,
      ite_true, dite_false, hmt]
    congr 1
    rw [hsub.2]; simp; ring

/-- Packing does not overflow for values below `2^K` when `K` fits the exponent range. -/
theorem unpack_pack_finite_of_lt {s : Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (hc : IsCanonical spec (.finite s m e hm)) (K : ℤ) (hv : (m : ℝ) * 2 ^ e < 2 ^ K)
    (hK : K + spec.exponentBias + spec.mantissaBitsWithoutImplicit + 1 ≤ 2 ^ spec.exponentBits) :
    UnpackedFloat.unpack spec (UnpackedFloat.pack spec (.finite s m e hm)) = .finite s m e hm := by
  apply unpack_pack_finite_of_fitsExponentRange hc
  have h1 : (2 : ℝ) ^ e < 2 ^ K := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [(by positivity : (0 : ℝ) < 2 ^ e)]
  have heK : e < K := (zpow_lt_zpow_iff_right₀ (by norm_num)).mp h1
  have hmin := hc.1
  rw [Format.minExponent_eq] at hmin
  unfold FitsExponentRange
  have : ((2 ^ spec.exponentBits : ℕ) : ℤ) = 2 ^ spec.exponentBits := by push_cast; rfl
  omega

/-- A canonical finite float within the format's largest finite magnitude does not overflow. -/
theorem fitsExponentRange_of_abs_toReal_le {s : Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (hc : IsCanonical spec (.finite s m e hm)) (h : |toReal (.finite s m e hm)| ≤ spec.maxFinite) :
    FitsExponentRange spec e := by
  rw [fitsExponentRange_iff]
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨hmin, -, hlow⟩ := hc
  rcases hlow with hlow | rfl
  · have hp := Format.two_le_mantissaBits spec
    have h2 : (0 : ℝ) < 2 := by norm_num
    have he : (2 : ℝ) ^ (spec.maxExponentBound + 1) ≤ 2 ^ e :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hm' : (2 : ℝ) ^ (spec.mantissaBits - 1) ≤ m := by exact_mod_cast hlow
    have habs : |toReal (.finite s m e hm)| = m * 2 ^ e := by
      simp only [toReal, abs_mul, Sign.abs_toReal, one_mul, Nat.abs_cast]
      rw [abs_of_pos (zpow_pos h2 _)]
    rw [habs, Format.maxFinite] at h
    have hpow : (2 : ℝ) ^ spec.mantissaBits = 2 ^ (spec.mantissaBits - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    have hE : (2 : ℝ) ^ (spec.maxExponentBound + 1) = 2 ^ spec.maxExponentBound * 2 := by
      rw [zpow_add_one₀ h2.ne']
    have hpos : (0 : ℝ) < 2 ^ spec.maxExponentBound := zpow_pos h2 _
    nlinarith [mul_le_mul hm' he (zpow_pos h2 _).le (by positivity)]
  · exact absurd (Format.minExponent_le_maxExponentBound spec) (not_le.2 hlt)

/-- Packing and unpacking a canonical finite float within the finite magnitude limit is lossless. -/
theorem unpack_pack_of_abs_toReal_le {r : UnpackedFloat} (hr : IsCanonical spec r)
    (hf : r.IsFinite) (h : |toReal r| ≤ spec.maxFinite) :
    unpack spec (pack spec r) = r := by
  cases r with
  | notANumber => simp [IsFinite, isFinite] at hf
  | infinity s => simp [IsFinite, isFinite] at hf
  | zero s => exact unpack_pack_zero s
  | finite s m e hm =>
    exact unpack_pack_finite_of_fitsExponentRange hr (fitsExponentRange_of_abs_toReal_le hr h)

theorem unpack_pack_finite {s : Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (hc : IsCanonical spec (.finite s m e hm)) :
    unpack spec (pack spec (.finite s m e hm)) = .finite s m e hm ∨
      unpack spec (pack spec (.finite s m e hm)) = .infinity s := by
  by_cases hno : FitsExponentRange spec e
  · exact Or.inl (unpack_pack_finite_of_fitsExponentRange hc hno)
  · right
    unfold pack
    simp only
    unfold FitsExponentRange at hno
    simp only [show 2 ^ spec.exponentBits ≤ (e + ↑spec.exponentBias +
      ↑spec.mantissaBitsWithoutImplicit).toNat + 1 by omega, ↓reduceIte]
    exact unpack_pack_infinity s

/-- The exponent of a finite value unpacked from a stored bit pattern fits the format. -/
theorem fitsExponentRange_of_unpack_eq_finite (spec : Format) [Fact (2 ≤ spec.exponentBits)] (b :
  BitVec spec.numBits) {s : Sign} {m : ℕ} {e : ℤ}
    {hm : 0 < m} (h : unpack spec b = .finite s m e hm) : FitsExponentRange spec e := by
  have heb := (Fact.out (p := 2 ≤ spec.exponentBits))
  have hmw := spec.hm
  have h1 : 1 ≤ 2 ^ (spec.exponentBits - 1) := Nat.one_le_two_pow
  have hbias : ((spec.exponentBias : ℕ) : ℤ) = 2 ^ (spec.exponentBits - 1) - 1 := by
    unfold Format.exponentBias; push_cast [h1]; ring
  have hEpos : 4 ≤ 2 ^ spec.exponentBits := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) heb
  unfold unpack at h
  simp only at h
  unfold FitsExponentRange
  split at h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
      · next h0 _ =>
        cases h
        rw [h0, BitVec.toNat_zero]
        rw [show ((0 : ℕ) : ℤ) - (↑spec.exponentBias + ↑spec.mantissaBitsWithoutImplicit) + 1 +
          ↑spec.exponentBias + ↑spec.mantissaBitsWithoutImplicit = 1 by push_cast; ring]
        simp only [Int.toNat_one]; omega
    · next h1 h0 =>
      cases h
      have hlt := (unpackExponent b).isLt
      have hne : (unpackExponent b).toNat ≠ 2 ^ spec.exponentBits - 1 := by
        intro h'; apply h1; apply BitVec.eq_of_toNat_eq
        rw [h', BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
      rw [show ((unpackExponent b).toNat : ℤ) - (↑spec.exponentBias +
          ↑spec.mantissaBitsWithoutImplicit) + ↑spec.exponentBias +
          ↑spec.mantissaBitsWithoutImplicit = (unpackExponent b).toNat by ring]
      simp only [Int.toNat_natCast]
      omega

/-- Changing the sign of an unpacked float and packing it again is lossless. -/
theorem unpack_pack_resign (spec : Format) [Fact (2 ≤ spec.exponentBits)] (b : BitVec
  spec.numBits) {s : Sign} {m : ℕ} {e : ℤ}
    {hm : 0 < m} (h : unpack spec b = .finite s m e hm) (s' : Sign) :
    unpack spec (pack spec (.finite s' m e hm)) = .finite s' m e hm := by
  have hc := unpack_isCanonical spec b
  rw [h] at hc
  exact unpack_pack_finite_of_fitsExponentRange hc (fitsExponentRange_of_unpack_eq_finite spec b h)

/-- Unpacking a bit pattern, packing and unpacking again gives the same float. -/
theorem unpack_pack_unpack (spec : Format) [Fact (2 ≤ spec.exponentBits)] (b : BitVec
  spec.numBits) :
    unpack spec (pack spec (unpack spec b)) = unpack spec b := by
  generalize h : unpack spec b = x
  cases x with
  | infinity s => exact unpack_pack_infinity s
  | notANumber => exact unpack_pack_nan
  | zero s => exact unpack_pack_zero s
  | finite s m e hm => exact unpack_pack_resign spec b h s


end Float.Model.UnpackedFloat

namespace Float.Model.Format

open Float.Model.BinaryRounding

/-- The largest finite magnitude belongs to the lower-exponent binary grid. -/
theorem isBinaryFloat_maxFinite (fmt : Format) [Fact (2 ≤ fmt.exponentBits)] :
    IsBinaryFloat fmt.mantissaBits fmt.minExponent fmt.maxFinite := by
  refine ⟨(2 : ℤ) ^ fmt.mantissaBits - 1, fmt.maxExponentBound,
    Format.minExponent_le_maxExponentBound fmt, ?_, ?_⟩
  · have hp : (1 : ℤ) ≤ 2 ^ fmt.mantissaBits := by
      exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ fmt.mantissaBits)
    rw [abs_of_nonneg (by omega)]
    omega
  · simp only [Format.maxFinite, Int.cast_sub, Int.cast_pow, Int.cast_ofNat,
      Int.cast_one]

end Float.Model.Format
