/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.Underflow
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The CG residual cache with underflow

The registered stored and matrix-free CG trees compute each cached squared residual with
`dot tag dst r off r off N`. This file analyzes that actual kernel under a range-aware
mixed-error contract. It retains the executed kernel, the returned word, and its final
single-cell store write. No new recurrence or program is introduced.

Underflow changes the meaning of the zero-cache guard: a computed zero certifies a small
residual, rather than an exactly zero residual. The existing relative-only whole-program
theorems remain unchanged. The certificate here bounds the decoded recursively updated
residual; it does not bound the mathematical residual of the computed iterate without a
residual-gap estimate. [Higham2002, §2.2 and §3.1].

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_cg_self_dot_of_absRelErr`:
  actual cached-residual execution, mixed error, and zero-cache residual certificate.
* `NLAlib.Computation.IsArithErrSem.exec_cg_self_dot_of_absRelErr_of_abs_le`:
  the same execution certificate from an input-only safe-radius condition.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u η : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}

/-- The actual squared-residual kernel of CG succeeds under a mixed-error arithmetic contract
and explicit range conditions. If $R=\|\mathbf{r}\|^2$ and $\nu$ is the decoded cache, then
$$\lvert R-\nu\rvert\le\bigl((1+u)^{2N}-1\bigr)R+
N(1+u)^{2N}(2+u)\eta\,.$$
If $2-(1+u)^{2N}>0$, a computed zero certifies
$$R\le\frac{N(1+u)^{2N}(2+u)\eta}{2-(1+u)^{2N}}\,.$$
The conclusion permits a nonzero residual when the cache vanishes. It holds also for the
empty kernel. This is a certificate for the recursive residual, not the true residual of the
computed iterate. Only the destination cell changes in the final store. -/
theorem IsArithErrSem.exec_cg_self_dot_of_absRelErr
    (I : Interp P ι K C) (tag : P)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K C)
    (N : ℕ) (dst : Cell ℕ ℕ) (r : ℕ) (off : IExp ℕ) (rv : ℕ → ℝ)
    (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (hr : ∀ i < N, ∃ w, st.store.read tag r (off.eval + i) = some w ∧ dec tag w = rv i)
    (hdr : dst.buf = r → ∀ i < N, dst.idx.eval ≠ off.eval + i)
    (hdst : ∃ v s, st.store.write tag dst.buf dst.idx.eval v = some s)
    (hsafe : ∀ k < N, ∀ s : ℕ → ℝ,
      IsDotTrace (fun _ => AbsRelErr (u tag) (η tag)) rv rv k s →
      safe tag (rv k * rv k) ∧ ∀ q, AbsRelErr (u tag) (η tag) (rv k * rv k) q →
        safe tag (s k + q)) :
    ∃ out w, exec I (dot tag dst r off r off (.const N)).run st = some out ∧
      st.store.write tag dst.buf dst.idx.eval w = some out.store ∧
      out.store.read tag dst.buf dst.idx.eval = some w ∧
      AbsRelErr ((1 + u tag) ^ (2 * N) - 1)
        (N * (1 + u tag) ^ (2 * N) * (2 + u tag) * η tag)
        (‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2) (dec tag w) ∧
      (0 < 2 - (1 + u tag) ^ (2 * N) → dec tag w = 0 →
        ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 ≤
          (N * (1 + u tag) ^ (2 * N) * (2 + u tag) * η tag) /
            (2 - (1 + u tag) ^ (2 * N))) := by
  obtain ⟨out, w, hrun, hwrite, herr⟩ :=
    h.exec_dot_abs_sum_mul_sub_le_of_absRelErr I tag hz st
      dst r off r off (.const N) rv rv hu hη hr hr hdr hdr hdst hsafe
  have hnorm : ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 =
      ∑ k ∈ Finset.range N, rv k * rv k := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [WithLp.ofLp_toLp, pow_two] using
      Fin.sum_univ_eq_sum_range (fun k => rv k * rv k) N
  have hsum : ∑ k ∈ Finset.range N, |rv k * rv k| =
      ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 := by
    rw [hnorm]
    exact Finset.sum_congr rfl fun k _ => abs_of_nonneg (mul_self_nonneg _)
  have hR : 0 ≤ ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 := sq_nonneg _
  have herror : AbsRelErr ((1 + u tag) ^ (2 * N) - 1)
      (N * (1 + u tag) ^ (2 * N) * (2 + u tag) * η tag)
      (‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2) (dec tag w) := by
    simp only [AbsRelErr, abs_of_nonneg hR]
    simpa only [IExp.eval, ← hnorm, hsum] using herr
  refine ⟨out, w, hrun, hwrite, Store.read_of_write_eq_some hwrite, herror, ?_⟩
  intro hsmall hzero
  have hzeroerror := herror
  rw [hzero] at hzeroerror
  have hbound := hzeroerror.abs_le_of_eq_zero (by linarith)
  rw [abs_of_nonneg hR,
    show 1 - ((1 + u tag) ^ (2 * N) - 1) = 2 - (1 + u tag) ^ (2 * N) by ring] at hbound
  exact hbound

/-- The CG squared-residual kernel executes from an input-only range certificate. Suppose
every exact value of magnitude at most $L$ is safe for the scalar backend, and put
$P=(1+u)^{2N}$ and $D=NP(2+u)\eta$. The condition
$P\|\mathbf{r}\|^2+D\le L$ certifies every intermediate product and accumulation.
The actual cache $\nu$ has error at most $(P-1)\|\mathbf{r}\|^2+D$; if $P<2$, its vanishing
certifies $\|\mathbf{r}\|^2\le D/(2-P)$. Relative and absolute allowances must be nonnegative.
The theorem retains actual execution and the destination write/read, including dimension zero.
It makes no assumption about measured intermediate values or a native floating-point runtime. -/
theorem IsArithErrSem.exec_cg_self_dot_of_absRelErr_of_abs_le
    (I : Interp P ι K C) (tag : P)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K C)
    (N : ℕ) (dst : Cell ℕ ℕ) (r : ℕ) (off : IExp ℕ) (rv : ℕ → ℝ)
    (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (hr : ∀ i < N, ∃ w, st.store.read tag r (off.eval + i) = some w ∧ dec tag w = rv i)
    (hdr : dst.buf = r → ∀ i < N, dst.idx.eval ≠ off.eval + i)
    (hdst : ∃ v s, st.store.write tag dst.buf dst.idx.eval v = some s)
    (L : ℝ) (hsafe : ∀ a, |a| ≤ L → safe tag a)
    (hrange : (1 + u tag) ^ (2 * N) * ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 +
      N * (1 + u tag) ^ (2 * N) * (2 + u tag) * η tag ≤ L) :
    ∃ out w, exec I (dot tag dst r off r off (.const N)).run st = some out ∧
      st.store.write tag dst.buf dst.idx.eval w = some out.store ∧
      out.store.read tag dst.buf dst.idx.eval = some w ∧
      AbsRelErr ((1 + u tag) ^ (2 * N) - 1)
        (N * (1 + u tag) ^ (2 * N) * (2 + u tag) * η tag)
        (‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2) (dec tag w) ∧
      (0 < 2 - (1 + u tag) ^ (2 * N) → dec tag w = 0 →
        ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 ≤
          (N * (1 + u tag) ^ (2 * N) * (2 + u tag) * η tag) /
            (2 - (1 + u tag) ^ (2 * N))) := by
  have hsum : (∑ k ∈ Finset.range N, |rv k * rv k|) =
      ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => |rv k * rv k|) N,
      EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun k _ => by
      simpa only [pow_two] using abs_of_nonneg (mul_self_nonneg (rv k))
  have hsafe' : ∀ k < N, ∀ s : ℕ → ℝ,
      IsDotTrace (fun _ => AbsRelErr (u tag) (η tag)) rv rv k s →
      safe tag (rv k * rv k) ∧ ∀ q, AbsRelErr (u tag) (η tag) (rv k * rv k) q →
        safe tag (s k + q) := by
    intro k hk s htrace
    constructor
    · apply hsafe
      have hterm : |rv k * rv k| ≤ ∑ j ∈ Finset.range N, |rv j * rv j| :=
        Finset.single_le_sum (f := fun j => |rv j * rv j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hk)
      rw [hsum] at hterm
      have hP : 1 ≤ (1 + u tag) ^ (2 * N) := one_le_pow₀ (by linarith)
      have hR : 0 ≤ ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 := sq_nonneg _
      have hD : 0 ≤ (N : ℝ) * (1 + u tag) ^ (2 * N) * (2 + u tag) * η tag :=
        by positivity
      nlinarith
    · intro q hq
      apply hsafe
      have hacc := htrace.abs_add_le_of_absRelErr hu hη hk hq
      rw [hsum] at hacc
      exact hacc.trans hrange
  exact h.exec_cg_self_dot_of_absRelErr I tag hz st N dst r off rv
    hu hη hr hdr hdst hsafe'

end NLAlib.Computation
