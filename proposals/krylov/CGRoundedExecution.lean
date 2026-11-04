/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import proposals.krylov.CGImplementationRoundoff
public import NLAlib.Krylov.LinearSystems.CGProgramDirection
public import NLAlib.Computation.ScalarFrames
public import NLAlib.Matrix.Computation.BLAS
public import NLAlib.Computation.BLAS.Normalization

/-!
# Rounded execution defects of the fixed CG implementation

The same canonical inline direction update satisfies its normwise CG defect bound, derived
from the primitive relative-error contract and actual stored words. Full multiplication and
addition cross terms are retained through the existing two-operation rounding-factor theorem.
No rounded whole-solver target or horizon success theorem is asserted here.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_cg_direction_update_norm_sub_le`: actual direction defect.
-/

@[expose] public section

namespace NLAlib.Computation

open scoped Matrix

private theorem norm_axpy_sub_le_of_relErr {N : ℕ} {u a : ℝ} {x y q z : Fin N → ℝ}
    (hu : 0 ≤ u) (hu2 : 2 * u < 1)
    (hq : ∀ i, RelErr u (a * x i) (q i)) (hz : ∀ i, RelErr u (q i + y i) (z i)) :
    ‖WithLp.toLp 2 (fun i => z i - (y i + a * x i))‖ ≤
      roundingFactor 2 u * (‖WithLp.toLp 2 y‖ + |a| * ‖WithLp.toLp 2 x‖) := by
  have hu1 : u < 1 := by linarith
  have hγ := roundingFactor_nonneg (n := 2) hu hu1
  have huγ : u ≤ roundingFactor 2 u := by
    have htwo : 2 * u ≤ roundingFactor 2 u := le_roundingFactor hu hu1
    linarith
  have hpoint (i : Fin N) : |z i - (y i + a * x i)| ≤
      roundingFactor 2 u * (|y i| + |a| * |x i|) := by
    obtain ⟨θ, δ, hθ, hδ, he⟩ :=
      exists_eq_mul_one_add_add_mul_one_add_of_relErr (hq i) (hz i) hu1
    rw [he]
    calc
      _ = |y i * δ + a * x i * θ| := by congr 1; ring
      _ ≤ |y i * δ| + |a * x i * θ| := abs_add_le _ _
      _ ≤ |y i| * roundingFactor 2 u + (|a| * |x i|) * roundingFactor 2 u := by
        simp only [abs_mul]
        gcongr
        exact hδ.trans huγ
      _ = _ := by ring
  have hnorm := EuclideanSpace.norm_toLp_le_norm_toLp
    (x := fun i : Fin N => z i - (y i + a * x i))
    (y := roundingFactor 2 u • ((fun i : Fin N => |y i|) + |a| • (fun i => |x i|)))
    (fun i => by
      change |z i - (y i + a * x i)| ≤ |roundingFactor 2 u * (|y i| + |a| * |x i|)|
      rw [abs_mul, abs_of_nonneg hγ,
        abs_of_nonneg (show 0 ≤ |y i| + |a| * |x i| by positivity)]
      exact hpoint i)
  have habs (v : Fin N → ℝ) : ‖WithLp.toLp 2 (fun i => |v i|)‖ = ‖WithLp.toLp 2 v‖ := by
    simp [EuclideanSpace.norm_eq]
  calc
    _ ≤ _ := hnorm
    _ = roundingFactor 2 u * ‖WithLp.toLp 2
        ((fun i : Fin N => |y i|) + |a| • (fun i => |x i|))‖ := by
      rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
    _ ≤ _ := by
      rw [WithLp.toLp_add, WithLp.toLp_smul]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hγ |>.trans_eq (by
        rw [norm_smul, Real.norm_eq_abs, abs_abs, habs, habs])

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ}

/-- The fixed inline direction loop produces an actual decoded next direction with its
normwise CG update defect. The original execution, state/count identity and complete cell
frame are retained. The two-operation factor includes the product of both rounding errors. -/
theorem IsRelErrSem.exec_cg_direction_update_norm_sub_le
    (I : Interp P ι K C) (tag : P) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (st : St P K C) (coeff tmp : Cell ℕ ℕ) (p r : ℕ) (n : IExp ℕ)
    (av : ℝ) (pv rv : ℕ → ℝ) (hu : 2 * u tag < 1)
    (hc : ∃ w, st.store.read tag coeff.buf coeff.idx.eval = some w ∧ dec tag w = av)
    (hp : ∀ i < n.eval, ∃ w, st.store.read tag p i = some w ∧ dec tag w = pv i)
    (hr : ∀ i < n.eval, ∃ w, st.store.read tag r i = some w ∧ dec tag w = rv i)
    (hpr : p ≠ r) (htp : tmp.buf ≠ p) (htr : tmp.buf ≠ r) (hcp : coeff.buf ≠ p)
    (htc : tmp.buf = coeff.buf → tmp.idx.eval ≠ coeff.idx.eval)
    (ht : ∃ w s, st.store.write tag tmp.buf tmp.idx.eval w = some s) :
    ∃ (out : St P K C) (W : Fin n.eval → K),
      exec I (Builder.forRange n fun i => do
        Builder.ins (.bin tag .mul tmp coeff ⟨p, .var i⟩)
        Builder.ins (.bin tag .add ⟨p, .var i⟩ ⟨r, .var i⟩ tmp)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out = { st with
        store := out.store
        cnt := st.cnt + n.eval • (I.charge (.bin tag .mul) + I.charge (.bin tag .add)) } ∧
      (∀ q b j, (q ≠ tag ∨ b ≠ p ∨ n.eval ≤ j) →
        (q ≠ tag ∨ b ≠ tmp.buf ∨ j ≠ tmp.idx.eval) →
        out.store.read q b j = st.store.read q b j) ∧
      (∀ i : Fin n.eval, out.store.read tag p i = some (W i)) ∧
      ‖WithLp.toLp 2 (fun i : Fin n.eval => (rv i + av * pv i) - dec tag (W i))‖ ≤
        roundingFactor 2 (u tag) *
          (‖WithLp.toLp 2 (fun i : Fin n.eval => rv i)‖ +
            |av| * ‖WithLp.toLp 2 (fun i : Fin n.eval => pv i)‖) := by
  classical
  obtain ⟨out, hrun, hshape, hstate, hframe, hout⟩ :=
    h.exec_cg_direction_update I tag st coeff tmp p r n av pv rv
      hc hp hr hpr htp htr hcp htc ht
  choose W q hread hmul hadd using fun i : Fin n.eval => hout i i.isLt
  refine ⟨out, W, hrun, hshape, hstate, hframe, hread, ?_⟩
  change ‖WithLp.toLp 2 ((fun i : Fin n.eval => rv i + av * pv i) -
    (fun i => dec tag (W i)))‖ ≤ _
  rw [WithLp.toLp_sub, norm_sub_rev, ← WithLp.toLp_sub]
  exact norm_axpy_sub_le_of_relErr (h.nonneg trivial) hu hmul
    (fun i => by simpa only [add_comm] using hadd i)

end NLAlib.Computation

namespace NLAlib

/-- The input-only implementation budget supplies the primitive dot/division windows and
dominates the self-dot rounding factor. No measured execution quantity occurs here. -/
theorem cgImplementationRoundoffBound_kernel_bounds {N : ℕ} (hN : 0 < N)
    {u : ℝ} (hu : 0 ≤ u) (hsmall : cgImplementationRoundoffBound N u ≤ 1 / 100) :
    (N : ℝ) * u < 1 ∧ 2 * u < 1 ∧
      Computation.roundingFactor N u ≤ cgImplementationRoundoffBound N u := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNu0 : 0 ≤ (N : ℝ) * u := by positivity
  have h4Nu : 4 * N * u ≤ cgImplementationRoundoffBound N u := by
    rw [cgImplementationRoundoffBound_def]
    nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) ^ 2 - N by nlinarith) hu]
  have h4u := four_mul_le_cgImplementationRoundoffBound hN hu
  refine ⟨by linarith, by linarith, ?_⟩
  exact (roundingFactor_le_two_mul_of_cgImplementationRoundoffBound_le hN hu hsmall).trans
    (by linarith)

end NLAlib

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ}

/-- The actual self-dot instruction supplies the cached-residual error field with the
input-only CG precision budget. Its decoded value is nonnegative and vanishes exactly for a
zero residual; no Euclidean monotonicity or desired local-error premise is used. -/
theorem IsRelErrSem.exec_cg_self_dot (I : Interp P ι K C) (tag : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (xs : ℕ → ℝ)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hx : ∀ i < N, ∃ w, st.store.read tag x (xo.eval + i) = some w ∧ dec tag w = xs i)
    (hdx : dst.buf = x → ∀ i < N, dst.idx.eval ≠ xo.eval + i)
    (hdst : ∃ v s, st.store.write tag dst.buf dst.idx.eval v = some s) :
    ∃ out w θ, exec I (dot tag dst x xo x xo (.const N)).run st = some out ∧
      st.store.write tag dst.buf dst.idx.eval w = some out.store ∧
      dec tag w = ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ ^ 2 * (1 + θ) ∧
      |θ| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 ≤ dec tag w ∧
      (dec tag w = 0 ↔ (fun i : Fin N => xs i) = 0) := by
  have hu := h.nonneg (p := tag) trivial
  obtain ⟨hNu, _, hγ⟩ := cgImplementationRoundoffBound_kernel_bounds hN hu hsmall
  obtain ⟨out, w, hrun, hwrite, θ, hθ, heq⟩ :=
    h.exec_dot_self_relErr I tag st hz dst x xo (.const N) xs hNu hx hdx hdst
  have hθ' := hθ.trans hγ
  have hfactor : 0 < 1 + θ := by linarith [(abs_le.mp hθ').1]
  refine ⟨out, w, θ, hrun, hwrite, heq, hθ', ?_, ?_⟩
  · rw [heq]
    exact mul_nonneg (sq_nonneg _) hfactor.le
  · rw [heq, mul_eq_zero, or_iff_left hfactor.ne', sq_eq_zero_iff, norm_eq_zero,
      WithLp.toLp_eq_zero]
    rfl

/-- A scalar division of actual initialized words succeeds when its decoded divisor is
nonzero, and supplies its relative-error witness directly from the primitive contract.
For CG these nonzero divisors are extracted from the actual curvature and stop guards. -/
theorem IsRelErrSem.exec_cg_division (I : Interp P ι K C) (tag : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C)
    (dst x y : Cell ℕ ℕ) (wx wy : K)
    (hx : st.store.read tag x.buf x.idx.eval = some wx)
    (hy : st.store.read tag y.buf y.idx.eval = some wy) (hne : dec tag wy ≠ 0)
    (hd : ∃ len, st.store.shape[dst.buf]? = some (tag, len) ∧ dst.idx.eval < len) :
    ∃ (out : St P K C) (w : K), exec I (Builder.ins (.bin tag .div dst x y)).run st = some out ∧
      out = { st with store := out.store, cnt := st.cnt + I.charge (.bin tag .div) } ∧
      out.store.shape = st.store.shape ∧ out.store.read tag dst.buf dst.idx.eval = some w ∧
      RelErr (u tag) (dec tag wx / dec tag wy) (dec tag w) ∧
      ∀ q buf idx, (q ≠ tag ∨ buf ≠ dst.buf ∨ idx ≠ dst.idx.eval) →
        out.store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨w, hsem⟩ := h.bin_ok tag .div wx wy trivial (fun _ => hne) trivial
  obtain ⟨store, hw, hrun, hshape, hread, hframe⟩ :=
    exec_scalar_bin I tag st .div dst x y wx wy w hx hy hsem hd
  exact ⟨{ st with store := store, cnt := st.cnt + I.charge (.bin tag .div) },
    w, hrun, rfl, hshape, hread, h.bin_err tag .div wx wy w trivial hsem, hframe⟩

/-- A true actual strict comparison exposes initialized operand words and strict order of
their decodings. In CG this supplies positive curvature from the executed zero/curvature guard. -/
theorem IsRelErrSem.decoded_lt_of_cmpStep_eq_some_true (I : Interp P ι K C) (tag : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (st out : St P K C)
    (x y : Cell ℕ ℕ) (hrun : cmpStep I tag .lt x y st = some (true, out)) :
    ∃ wx wy, st.store.read tag x.buf x.idx.eval = some wx ∧
      st.store.read tag y.buf y.idx.eval = some wy ∧ dec tag wx < dec tag wy := by
  simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hrun
  obtain ⟨wx, hx, wy, hy, flag, hsem, hpair⟩ := hrun
  have hflag : flag = true := congrArg Prod.fst hpair
  have hdec : decide (dec tag wx < dec tag wy) = true :=
    (Option.some.inj ((h.cmp_lt tag wx wy).symm.trans hsem)).trans hflag
  exact ⟨wx, wy, hx, hy, of_decide_eq_true hdec⟩

/-- A false actual equality comparison exposes initialized words with unequal decodings.
Combining this with the self-dot nonnegativity theorem proves positivity of an active cache. -/
theorem IsRelErrSem.decoded_ne_of_cmpStep_eq_some_false (I : Interp P ι K C) (tag : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (st out : St P K C)
    (x y : Cell ℕ ℕ) (hrun : cmpStep I tag .eq x y st = some (false, out)) :
    ∃ wx wy, st.store.read tag x.buf x.idx.eval = some wx ∧
      st.store.read tag y.buf y.idx.eval = some wy ∧ dec tag wx ≠ dec tag wy := by
  simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hrun
  obtain ⟨wx, hx, wy, hy, flag, hsem, hpair⟩ := hrun
  have hflag : flag = false := congrArg Prod.fst hpair
  have hdec : decide (dec tag wx = dec tag wy) = false :=
    (Option.some.inj ((h.cmp_eq tag wx wy).symm.trans hsem)).trans hflag
  exact ⟨wx, wy, hx, hy, of_decide_eq_false hdec⟩

/-- The actual zero-offset CG axpy kernel returns its finite decoded output, full buffer
frame and the input-only implementation error allowance. This serves both x and r updates. -/
theorem IsRelErrSem.exec_cg_axpy (I : Interp P ι K C) (tag : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C)
    (N : ℕ) (a : Cell ℕ ℕ) (x y : ℕ) (av : ℝ) (xs ys : Fin N → ℝ)
    (ha : ∃ w, st.store.read tag a.buf a.idx.eval = some w ∧ dec tag w = av)
    (hx : ∀ i : Fin N, ∃ w, st.store.read tag x i = some w ∧ dec tag w = xs i)
    (hy : ∀ i : Fin N, ∃ w, st.store.read tag y i = some w ∧ dec tag w = ys i)
    (hxy : x ≠ y) (hay : a.buf ≠ y) (hN : 0 < N)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (W : Fin N → K),
      exec I (axpy tag a x 0 y 0 (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag y i = some (W i)) ∧
      ‖WithLp.toLp 2 (fun i : Fin N => ys i + av * xs i - dec tag (W i))‖ ≤
        cgImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 ys‖ + |av| * ‖WithLp.toLp 2 xs‖) ∧
      ∀ q buf idx, buf ≠ y → out.store.read q buf idx = st.store.read q buf idx := by
  have hu := h.nonneg (p := tag) trivial
  obtain ⟨_, hu2, _⟩ := cgImplementationRoundoffBound_kernel_bounds hN hu hsmall
  let xv : ℕ → ℝ := fun i => if hi : i < N then xs ⟨i, hi⟩ else 0
  let yv : ℕ → ℝ := fun i => if hi : i < N then ys ⟨i, hi⟩ else 0
  have hx' (i : ℕ) (hi : i < N) :
      ∃ w, st.store.read tag x (0 + i) = some w ∧ dec tag w = xv i := by
    simpa only [zero_add, xv, dif_pos hi] using hx ⟨i, hi⟩
  have hy' (i : ℕ) (hi : i < N) :
      ∃ w, st.store.read tag y (0 + i) = some w ∧ dec tag w = yv i := by
    simpa only [zero_add, yv, dif_pos hi] using hy ⟨i, hi⟩
  obtain ⟨out, W, hrun, hwrite, herr⟩ := h.exec_axpy_norm_sub_le I tag st a x 0 y 0
    (.const N) av xv yv hu2 ha hx' hy' (fun he => (hay he).elim)
    (fun he => (hxy he).elim)
  have hxv : (fun i : Fin N => xv i) = xs := by funext i; simp only [xv, dif_pos i.isLt]
  have hyv : (fun i : Fin N => yv i) = ys := by funext i; simp only [yv, dif_pos i.isLt]
  refine ⟨out, fun i => W i, hrun, Store.shape_of_writeBlock_eq_some hwrite, ?_, ?_, ?_⟩
  · intro i
    simpa only [IExp.eval_zero, IExp.eval_const, zero_add, Array.getElem?_map,
      List.getElem?_toArray, List.getElem?_range i.isLt, Option.map_some] using
      Store.read_of_writeBlock_eq_some_of_lt (j := (i : ℕ)) hwrite (by simp [i.isLt])
  · have hfun : (fun i : Fin N => yv i + av * xv i - dec tag (W i)) =
        (fun i : Fin N => ys i + av * xs i - dec tag (W i)) := by
      funext i
      rw [← hyv, ← hxv]
    rw [IExp.eval_const, hfun, hxv, hyv] at herr
    exact herr.trans (mul_le_mul_of_nonneg_right
      (roundingFactor_two_le_cgImplementationRoundoffBound hN hu hsmall)
      (add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))))
  · intro q buf idx hb
    exact Store.read_of_writeBlock_eq_some_of_ne hwrite (Or.inl hb)

end NLAlib.Computation
