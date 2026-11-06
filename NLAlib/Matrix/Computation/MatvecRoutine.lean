/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.MatvecRoutine
public import NLAlib.Matrix.Computation.BLAS

/-!
# Dense matrix-vector routine certificates

The ordered scalar-loop dense product supplies the same routine contract as an accurate
external oracle. Its precision coefficient is derived from scalar rounding, with loaded
matrix entries as its backend storage precondition.

## Main results

* `NLAlib.Computation.IsRelErrSem.isMatvecRoutine_gemv`: the actual dense kernel certificate.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
    {u : P → ℝ} {dec : P → K → ℝ}

/-- The actual stored dense product is a certified matvec routine, with operator-error
coefficient given by the ordered rounding factor times the square root of the dimension
and the spectral norm. The destination is disjoint from both inputs. This is the existing
normwise kernel bound [Higham2002, (3.12)] with its execution frame retained. -/
theorem IsRelErrSem.isMatvecRoutine_gemv (I : Interp P ι K C) (tag : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (matrix src dst : ℕ)
    (aOff sOff dOff : IExp ℕ) (hn : (N : ℝ) * u tag < 1)
    (hda : dst ≠ matrix) (hdx : dst ≠ src) :
    IsMatvecRoutine I dec tag A
      (roundingFactor N (u tag) * Real.sqrt N * specNorm A)
      (fun store => HoldsDecoded store dec tag matrix aOff.eval A) src dst sOff dOff
      (gemv tag (.const N) (.const N) matrix aOff src sOff dst dOff) where
  composable := executionComposable_single I (fun _ => rfl)
  run st x hA hx hy := by
    obtain ⟨zero, hzero⟩ := h.lit_ok tag 0 trivial
    obtain ⟨out, W, hr, hw, he⟩ := h.exec_gemv_norm_sub_le_specNorm_mul I tag st hz
      (.const N) (.const N) matrix aOff src sOff dst dOff A x hn hA hx
      (fun he => (hda he).elim) (fun he => (hdx he).elim) (fun i hi => by
        obtain ⟨len, hlen, hlt⟩ := hy i hi
        exact ⟨zero, Store.exists_write_eq_some_of_getElem?_shape zero hlen hlt⟩)
    refine ⟨out, fun i => W i, hr, ?_, he⟩
    convert hw using 1
    congr 1
    apply Array.ext (by simp)
    intro i hi hj
    simp

end NLAlib.Computation
