/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BinaryFloatSem
public import NLAlib.Krylov.LinearSystems.CGProgramUnderflow

/-!
# CG residual computation in bounded binary floating point

The binary endpoint has fixed significand precision, bounded exponents, a subnormal grid,
and a chosen nearest-integer rounding rule. Its scalar accuracy and range-success laws are
proved from the quantizer. This file instantiates the actual residual-dot kernel used by
the registered CG trees, with an input-only bound that certifies every intermediate product
and accumulation lies in range.

This is a bounded floating-point numerical model. It does not assert equivalence to native
Lean `Float`, specify a native instruction cost, or analyze a complete CG loop. The result
distinguishes a cache rounded to zero from an exactly zero recursive residual.

## Main results

* `NLAlib.CGImplementation.exec_self_dot_of_sem_eq_binaryFloatSem`:
  actual bounded-binary residual computation, range control and zero-cache certificate.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation

/-- In a bounded binary format, the actual CG squared-residual kernel executes if its
input obeys $P\|\mathbf{r}\|^2+D\le M$, where
$u=2^{-p}$, $\eta=2^{e_{\min}}/2$, $P=(1+u)^{2N}$, $D=NP(2+u)\eta$ and $M$ is the largest
finite magnitude. The chosen integer rounding rule must approximate every real within
one half; ties may be resolved by any rule satisfying that property. The actual cache $\nu$
has error at most $(P-1)\|\mathbf{r}\|^2+D$; if $P<2$, a zero cache certifies
$\|\mathbf{r}\|^2\le D/(2-P)$. The theorem includes dimension zero and retains the kernel
execution and destination write/read. No backend arithmetic-error assumption or observed
intermediate-range hypothesis is needed. -/
theorem exec_self_dot_of_sem_eq_binaryFloatSem {P ι C : Type}
    [DecidableEq P] [AddMonoid C] (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (rounder : ℝ → ℤ)
    (hround : ∀ a, AbsRelErr 0 (1 / 2) a (rounder a : ℝ))
    (I : Interp P ι (BinaryFloat fmt) C) (tag : P)
    (hsem : I.sem = binaryFloatSem fmt he rounder hround)
    (st : St P (BinaryFloat fmt) C)
    (N : ℕ) (dst : Cell ℕ ℕ) (r : ℕ) (off : IExp ℕ) (rv : ℕ → ℝ)
    (hr : ∀ i < N, ∃ w, st.store.read tag r (off.eval + i) = some w ∧ w.val = rv i)
    (hdr : dst.buf = r → ∀ i < N, dst.idx.eval ≠ off.eval + i)
    (hdst : ∃ v s, st.store.write tag dst.buf dst.idx.eval v = some s)
    (hrange : (1 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) ^ (2 * N) *
        ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 +
      N * (1 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) ^ (2 * N) *
        (2 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) * ((2 : ℝ) ^ fmt.minExponent / 2) ≤
          fmt.maxFinite) :
    ∃ out w, exec I (dot tag dst r off r off (.const N)).run st = some out ∧
      st.store.write tag dst.buf dst.idx.eval w = some out.store ∧
      out.store.read tag dst.buf dst.idx.eval = some w ∧
      AbsRelErr ((1 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) ^ (2 * N) - 1)
        (N * (1 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) ^ (2 * N) *
          (2 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) * ((2 : ℝ) ^ fmt.minExponent / 2))
        (‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2) w.val ∧
      (0 < 2 - (1 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) ^ (2 * N) → w.val = 0 →
        ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 ≤
          (N * (1 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) ^ (2 * N) *
            (2 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) * ((2 : ℝ) ^ fmt.minExponent / 2)) /
              (2 - (1 + (2⁻¹ : ℝ) ^ fmt.mantissaBits) ^ (2 * N))) := by
  have h : IsArithErrSem (fun (_ : P) _ =>
      AbsRelErr ((2⁻¹ : ℝ) ^ fmt.mantissaBits) ((2 : ℝ) ^ fmt.minExponent / 2))
      (fun _ (x : BinaryFloat fmt) => x.val)
      (fun _ a => |a| ≤ fmt.maxFinite) I.sem := by
    rw [hsem]
    exact isArithErrSem_binaryFloatSem fmt he rounder hround
  have hz : AddsZeroExactly (fun (_ : P) (x : BinaryFloat fmt) => x.val) I.sem := by
    rw [hsem]
    exact addsZeroExactly_binaryFloatSem fmt he rounder hround
  exact h.exec_cg_self_dot_of_absRelErr_of_abs_le I tag hz st N dst r off rv
    (by positivity) (by positivity) hr hdr hdst (fmt.maxFinite) (fun _ ha => ha) hrange

end NLAlib.CGImplementation
