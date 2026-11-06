/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.FixedPoint
public import NLAlib.Krylov.LinearSystems.CGProgramUnderflow

/-!
# CG residual computation in bounded fixed-point arithmetic

The scalar endpoint has a finite carrier of signed integers of magnitude at most
$\mathit{limit}$, decoded on a grid of positive scale $s$. Its four arithmetic operations
have a proved absolute error allowance $1/s$ and succeed whenever the exact result lies
in the representable interval. This file instantiates the actual residual-dot kernel used
by both registered CG trees, without an abstract arithmetic assumption or a hypothesis on
observed intermediate states.

The input condition $\|\mathbf{r}\|^2+2N/s\le\mathit{limit}/s$ certifies every intermediate
product and accumulation is in range. This is a finite-format kernel result, not a complete
CG convergence theorem or a native integer/rational runtime bound.

## Main results

* `NLAlib.CGImplementation.exec_self_dot_of_sem_eq_fixedPointSem`:
  actual bounded fixed-point residual computation with an input-only range certificate.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation

/-- At positive scale $s$, the actual CG residual-dot kernel executes in bounded fixed-point
arithmetic when $\|\mathbf{r}\|^2+2N/s\le\mathit{limit}/s$. It writes a cache $\nu$ with
$\lvert\|\mathbf{r}\|^2-\nu\rvert\le2N/s$. A zero cache therefore certifies
$\|\mathbf{r}\|^2\le2N/s$, without asserting that the recursive residual is exactly zero.
The theorem includes the empty kernel and uses only input-based range conditions, explicit
layout conditions and the actual fixed-point semantics. -/
theorem exec_self_dot_of_sem_eq_fixedPointSem {P ι C : Type}
    [DecidableEq P] [AddMonoid C] (scale limit : ℕ) (hscale : 0 < scale)
    (I : Interp P ι (FixedPoint limit) C) (tag : P)
    (hsem : I.sem = fixedPointSem scale limit) (st : St P (FixedPoint limit) C)
    (N : ℕ) (dst : Cell ℕ ℕ) (r : ℕ) (off : IExp ℕ) (rv : ℕ → ℝ)
    (hr : ∀ i < N, ∃ w, st.store.read tag r (off.eval + i) = some w ∧
      fixedPointDecode scale w = rv i)
    (hdr : dst.buf = r → ∀ i < N, dst.idx.eval ≠ off.eval + i)
    (hdst : ∃ v s, st.store.write tag dst.buf dst.idx.eval v = some s)
    (hrange : ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 +
      2 * N / (scale : ℝ) ≤ (limit : ℝ) / (scale : ℝ)) :
    ∃ out w, exec I (dot tag dst r off r off (.const N)).run st = some out ∧
      st.store.write tag dst.buf dst.idx.eval w = some out.store ∧
      out.store.read tag dst.buf dst.idx.eval = some w ∧
      |‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 - fixedPointDecode scale w| ≤
        2 * N / (scale : ℝ) ∧
      (fixedPointDecode scale w = 0 →
        ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 ≤ 2 * N / (scale : ℝ)) := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hη : 0 ≤ 1 / (scale : ℝ) := le_of_lt (one_div_pos.mpr hs)
  have hsum : (∑ k ∈ Finset.range N, |rv k * rv k|) =
      ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => |rv k * rv k|) N,
      EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun k _ => by
      simpa only [pow_two] using abs_of_nonneg (mul_self_nonneg (rv k))
  have h : IsArithErrSem (fun (_ : P) _ => AbsRelErr 0 (1 / (scale : ℝ)))
      (fun _ => fixedPointDecode scale)
      (fun _ a => |a| ≤ (limit : ℝ) / (scale : ℝ)) I.sem := by
    rw [hsem]
    exact isArithErrSem_fixedPointSem scale limit hscale
  have hz : AddsZeroExactly (fun (_ : P) => fixedPointDecode scale) I.sem := by
    rw [hsem]
    exact addsZeroExactly_fixedPointSem scale limit hscale
  have hsafe : ∀ k < N, ∀ s : ℕ → ℝ,
      IsDotTrace (fun _ => AbsRelErr 0 (1 / (scale : ℝ))) rv rv k s →
      |rv k * rv k| ≤ (limit : ℝ) / (scale : ℝ) ∧
      ∀ q, AbsRelErr 0 (1 / (scale : ℝ)) (rv k * rv k) q →
        |s k + q| ≤ (limit : ℝ) / (scale : ℝ) := by
    intro k hk s htrace
    constructor
    · have hterm : |rv k * rv k| ≤ ∑ j ∈ Finset.range N, |rv j * rv j| :=
        Finset.single_le_sum (f := fun j => |rv j * rv j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hk)
      rw [hsum] at hterm
      have hpadding : 0 ≤ 2 * N / (scale : ℝ) := by positivity
      linarith
    · intro q hq
      have hacc := htrace.abs_add_le_of_absRelErr_zero hη hk hq
      rw [hsum] at hacc
      exact hacc.trans (by simpa only [mul_one_div] using hrange)
  obtain ⟨out, w, hrun, hwrite, hread, herr, _⟩ :=
    h.exec_cg_self_dot_of_absRelErr I tag hz st N dst r off rv
      (by norm_num) hη hr hdr hdst hsafe
  have herror : |‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 -
      fixedPointDecode scale w| ≤ 2 * N / (scale : ℝ) := by
    simp only [AbsRelErr, zero_add, one_pow, sub_self, zero_mul, add_zero, mul_one] at herr
    exact herr.trans_eq (by ring)
  refine ⟨out, w, hrun, hwrite, hread, herror, ?_⟩
  intro hcache
  have hR : 0 ≤ ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 := sq_nonneg _
  simpa only [hcache, sub_zero, abs_of_nonneg hR] using herror

end NLAlib.CGImplementation
