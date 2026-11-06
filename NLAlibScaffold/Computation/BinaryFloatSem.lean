/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BinaryFloatSem

/-!
# Exact integer literals in a bounded binary format (scaffold)

Statements for `NLAlib/Computation/BinaryFloatSem.lean` (stage COMPDYN M2, design note
`docs/design/Computation-DynamicPrograms.md`, §4.1 and "S1 implementation status"): bounded binary
arithmetic has exact integer literals below $2^p$, $p$ the precision, when the exponent $0$ is in
the format's range.

## Main results

* `NLAlib.Computation.isExactIntLit_binaryFloatSem`: exact integer literals of a bounded binary
  format.
-/

@[expose] public section

namespace NLAlib.Computation

open Float.Model

/-- **A bounded binary format has exact integer literals**: if $B < 2^p$, $p$ the precision of
`fmt` (`fmt.mantissaBits`), and the exponent $0$ lies in the range of the format (at least its
minimum exponent and at most its largest significand exponent), then the bounded binary semantics
`NLAlib.Computation.binaryFloatSem fmt he r hr`, decoding a word to its value, meets
`NLAlib.Computation.IsExactIntLit` at $B$: every natural number $k \le B$ is a represented value,
and binary rounding fixes it. No printed source.
Proof: `intro q k hk`; `k` is `NLAlib.Computation.IsBinaryRep fmt` with mantissa `k` and exponent
`0` (`zpow_zero`, `mul_one`, `|(k : ℤ)| < 2 ^ fmt.mantissaBits` from `hB`); so
`|(k : ℝ)| ≤ fmt.maxFinite` by `NLAlib.Computation.IsBinaryRep.abs_le`, the quantization succeeds
(`binaryFloatQuantize`, `dif_pos`), and its value is `k` by
`NLAlib.Computation.binaryFloatRound_eq_self` (`Rat.cast_natCast`). M, about 15 lines. -/
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

end NLAlib.Computation
