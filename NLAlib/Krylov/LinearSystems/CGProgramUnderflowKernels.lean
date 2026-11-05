/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramDirection
public import NLAlib.Computation.ScalarFrames
public import NLAlib.Computation.VectorErrors

/-!
# Actual CG scalar and direction updates with absolute errors

The fixed CG program's division and inline direction update are analyzed under the
existing arithmetic error contract, retaining explicit safe-range requirements. Every
error conclusion comes from the executed primitive operations. The direction error keeps
its absolute contribution, including a zero computed coefficient or a zero vector.

The results preserve the actual store effects and charged operation counts. A positive
exact quotient may round to zero; neither result asserts positivity of its output.

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_cg_division`: actual range-certified division.
* `NLAlib.Computation.IsArithErrSem.exec_cg_direction_update_norm_sub_le_of_absRelErr`:
  actual inline direction update with a mixed Euclidean error bound.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {dec : P → K → ℝ} {safe : P → ℝ → Prop}

/-- The actual CG division succeeds when its decoded divisor is nonzero and the exact
quotient is safe. The result retains the primitive error relation, the exact charged
state update, the output word and the complete cell frame. No sign or nonzero property
of the computed quotient is inferred. -/
theorem IsArithErrSem.exec_cg_division {err : P → BinOp → ℝ → ℝ → Prop}
    (I : Interp P ι K C) (tag : P) (h : IsArithErrSem err dec safe I.sem)
    (st : St P K C) (dst x y : Cell ℕ ℕ) (wx wy : K)
    (hx : st.store.read tag x.buf x.idx.eval = some wx)
    (hy : st.store.read tag y.buf y.idx.eval = some wy) (hne : dec tag wy ≠ 0)
    (hsafe : safe tag (dec tag wx / dec tag wy))
    (hd : ∃ len, st.store.shape[dst.buf]? = some (tag, len) ∧ dst.idx.eval < len) :
    ∃ (out : St P K C) (w : K), exec I (Builder.ins (.bin tag .div dst x y)).run st = some out ∧
      out = { st with store := out.store, cnt := st.cnt + I.charge (.bin tag .div) } ∧
      out.store.shape = st.store.shape ∧ out.store.read tag dst.buf dst.idx.eval = some w ∧
      err tag .div (dec tag wx / dec tag wy) (dec tag w) ∧
      ∀ q buf idx, (q ≠ tag ∨ buf ≠ dst.buf ∨ idx ≠ dst.idx.eval) →
        out.store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨w, hsem⟩ := h.bin_ok tag .div wx wy trivial (fun _ => hne) hsafe
  obtain ⟨store, hw, hrun, hshape, hread, hframe⟩ :=
    exec_scalar_bin I tag st .div dst x y wx wy w hx hy hsem hd
  exact ⟨{ st with store := store, cnt := st.cnt + I.charge (.bin tag .div) },
    w, hrun, rfl, hshape, hread, h.bin_err tag .div wx wy w trivial hsem, hframe⟩

/-- The actual inline CG direction update has Euclidean error at most
$$u\|\mathbf{r}\|+u(2+u)\lvert a\rvert\|\mathbf{p}\|+\sqrt{N}(2+u)\eta\,.$$
Both allowances are nonnegative. Every exact product and every next exact addition
allowed by its product error must be safe. The result preserves actual execution,
the exact multiplication/addition charge, memory usage and the cell frame.
The coefficient and vectors may be zero; no precision-smallness condition is imposed. -/
theorem IsArithErrSem.exec_cg_direction_update_norm_sub_le_of_absRelErr
    {u η : P → ℝ} (I : Interp P ι K C) (tag : P)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (st : St P K C) (coeff tmp : Cell ℕ ℕ) (p r : ℕ) (n : IExp ℕ)
    (av : ℝ) (pv rv : ℕ → ℝ) (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (hc : ∃ w, st.store.read tag coeff.buf coeff.idx.eval = some w ∧ dec tag w = av)
    (hp : ∀ i < n.eval, ∃ w, st.store.read tag p i = some w ∧ dec tag w = pv i)
    (hr : ∀ i < n.eval, ∃ w, st.store.read tag r i = some w ∧ dec tag w = rv i)
    (hpr : p ≠ r) (htp : tmp.buf ≠ p) (htr : tmp.buf ≠ r) (hcp : coeff.buf ≠ p)
    (htc : tmp.buf = coeff.buf → tmp.idx.eval ≠ coeff.idx.eval)
    (ht : ∃ w s, st.store.write tag tmp.buf tmp.idx.eval w = some s)
    (hsafe : ∀ i < n.eval, safe tag (av * pv i) ∧
      ∀ q, AbsRelErr (u tag) (η tag) (av * pv i) q → safe tag (rv i + q)) :
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
        u tag * ‖WithLp.toLp 2 (fun i : Fin n.eval => rv i)‖ +
        u tag * (2 + u tag) * |av| * ‖WithLp.toLp 2 (fun i : Fin n.eval => pv i)‖ +
        Real.sqrt n.eval * (2 + u tag) * η tag := by
  classical
  obtain ⟨out, hrun, hshape, hstate, hframe, hout⟩ :=
    h.exec_cg_direction_update I tag st coeff tmp p r n av pv rv
      hc hp hr hpr htp htr hcp htc ht hsafe
  choose W q hread hmul hadd using fun i : Fin n.eval => hout i i.isLt
  refine ⟨out, W, hrun, hshape, hstate, hframe, hread, ?_⟩
  have herr := norm_sub_add_smul_le_of_absRelErr hmul hadd hu hu hη hη
  exact herr.trans_eq (by simp only [Fintype.card_fin]; ring)

end NLAlib.Computation
