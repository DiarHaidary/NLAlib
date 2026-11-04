/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import proposals.krylov.CGRoundedExecution
public import NLAlib.Krylov.LinearSystems.CGProgramBody

/-!
# Rounded local CG phases from actual stores

The stored matvec and curvature dot of the fixed CG body produce the local defects of the
existing `CGRun` model. Their bounds follow from primitive arithmetic and the input-only
implementation budget. No desired trajectory or local defect is assumed.

## Main results

* `NLAlib.CGImplementation.exec_rounded_matvec`: actual product and its spectral error.
* `NLAlib.CGImplementation.exec_rounded_curvature`: actual curvature and its dot error.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation
open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ}

/-- The actual dense product phase preserves persistent CG cells and returns decoded product
cells with the `CGRun.norm_es_le` error, under the explicit input-only implementation budget. -/
theorem exec_rounded_matvec (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (sv : Fin N → ℝ),
      exec I (gemv tag (.const N) (.const N) 5 0 3 0 6 0).run st = some out ∧
      StoreContext tag dec N A b v ν status flag out.store ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 6 i = some w ∧ dec tag w = sv i) ∧
      ‖WithLp.toLp 2 (A *ᵥ v.p - sv)‖ ≤
        cgImplementationRoundoffBound N (u tag) * specNorm A * ‖WithLp.toLp 2 v.p‖ := by
  have hu := hsem.nonneg (p := tag) trivial
  obtain ⟨hNu, _, _⟩ := cgImplementationRoundoffBound_kernel_bounds hN hu hsmall
  obtain ⟨zero, _, _⟩ := h.zero
  have hd (i : ℕ) (hi : i < N) : ∃ w s, st.store.write tag 6 i w = some s := by
    obtain ⟨store, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape zero
      (show st.store.shape[6]? = some (tag, N) by simp [h.shape, workspaceShape]) hi
    exact ⟨zero, store, hw⟩
  obtain ⟨out, W, hrun, hwrite, herr⟩ := hsem.exec_gemv_norm_sub_le_specNorm_mul I tag st
    hz (.const N) (.const N) 5 0 3 0 6 0 A v.p hNu h.matrix
    (by simpa only [IExp.eval_zero, IExp.eval_const, zero_add] using h.direction)
    (by norm_num) (by norm_num) (by simpa only [IExp.eval_zero, IExp.eval_const, zero_add] using hd)
  have hframe (q : P) (buf idx : ℕ) (hb : buf ≠ 6) :
      out.store.read q buf idx = st.store.read q buf idx :=
    Store.read_of_writeBlock_eq_some_of_ne hwrite (Or.inl hb)
  have hctx : StoreContext tag dec N A b v ν status flag out.store := by
    apply h.preserve_frame (Store.shape_of_writeBlock_eq_some hwrite)
    intro buf idx hcell
    apply hframe tag buf idx
    rcases hcell with hb | ⟨rfl, _⟩ <;> omega
  refine ⟨out, fun i => dec tag (W i), hrun, hctx, ?_, herr.trans ?_⟩
  · intro i
    refine ⟨W i, ?_, rfl⟩
    simpa only [IExp.eval_zero, IExp.eval_const, zero_add, Array.getElem?_map,
      List.getElem?_toArray,
      List.getElem?_range i.isLt, Option.map_some] using
      Store.read_of_writeBlock_eq_some_of_lt (j := (i : ℕ)) hwrite
        (by simp [i.isLt])
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (roundingFactor_mul_sqrt_le_cgImplementationRoundoffBound hN hu hsmall)
        (specNorm_nonneg A)) (norm_nonneg _)

/-- The actual curvature dot contributes only its own dot-product defect against the
already computed product. The matvec error is not counted again in `CGRun.abs_eμ_le`. -/
theorem exec_rounded_curvature (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (v : CGState ℝ (Fin N)) (ν status flag : ℝ) (sv : Fin N → ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store)
    (hs : ∀ i : Fin N, ∃ w, st.store.read tag 6 i = some w ∧ dec tag w = sv i)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (μ : ℝ),
      exec I (dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)).run st = some out ∧
      StoreContext tag dec N A b v ν status flag out.store ∧
      (∃ w, out.store.read tag 7 2 = some w ∧ dec tag w = μ) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 6 i = some w ∧ dec tag w = sv i) ∧
      |v.p ⬝ᵥ sv - μ| ≤ cgImplementationRoundoffBound N (u tag) *
        ‖WithLp.toLp 2 v.p‖ * ‖WithLp.toLp 2 sv‖ := by
  have hu := hsem.nonneg (p := tag) trivial
  obtain ⟨hNu, _, hγ⟩ := cgImplementationRoundoffBound_kernel_bounds hN hu hsmall
  let pv : ℕ → ℝ := fun i => if hi : i < N then v.p ⟨i, hi⟩ else 0
  let sx : ℕ → ℝ := fun i => if hi : i < N then sv ⟨i, hi⟩ else 0
  have hp (i : ℕ) (hi : i < N) :
      ∃ w, st.store.read tag 3 (0 + i) = some w ∧ dec tag w = pv i := by
    simpa only [zero_add, pv, dif_pos hi] using h.direction ⟨i, hi⟩
  have hs' (i : ℕ) (hi : i < N) :
      ∃ w, st.store.read tag 6 (0 + i) = some w ∧ dec tag w = sx i := by
    simpa only [zero_add, sx, dif_pos hi] using hs ⟨i, hi⟩
  obtain ⟨zero, _, _⟩ := h.zero
  obtain ⟨scratch, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape zero
    (show st.store.shape[7]? = some (tag, 9) by simp [h.shape, workspaceShape])
    (show 2 < 9 by norm_num)
  obtain ⟨out, w, hrun, hwrite, herr⟩ := hsem.exec_dot_abs_dotProduct_sub_le I tag st
    hz ⟨7, 2⟩ 3 0 6 0 (.const N) pv sx hNu hp hs' (by norm_num) (by norm_num)
    ⟨zero, scratch, hw⟩
  have hpv : (fun i : Fin N => pv i) = v.p := by funext i; simp only [pv, dif_pos i.isLt]
  have hsv : (fun i : Fin N => sx i) = sv := by funext i; simp only [sx, dif_pos i.isLt]
  refine ⟨out, dec tag w, hrun, h.preserve_scalar_write (by norm_num) (by norm_num) hwrite,
    ⟨w, Store.read_of_write_eq_some hwrite, rfl⟩, ?_, ?_⟩
  · intro i
    obtain ⟨word, hread, hdec⟩ := hs i
    exact ⟨word, (Store.read_of_write_eq_some_of_ne hwrite (Or.inl (by norm_num))).trans hread,
      hdec⟩
  · simp only [IExp.eval_const, hpv, hsv] at herr
    exact herr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hγ (norm_nonneg _)) (norm_nonneg _))

/-- The actual step-length division supplies its `CGRun.γ_eq` witness and positive decoded
coefficient. Positivity of the two cached operands is supplied by the actual branch facts. -/
theorem exec_rounded_step_length (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag μ : ℝ) (h : StoreContext tag dec N A b v ν status flag st.store)
    (hμ : ∃ w, st.store.read tag 7 2 = some w ∧ dec tag w = μ)
    (hνpos : 0 < ν) (hμpos : 0 < μ) (hN : 0 < N)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (γ eγ : ℝ),
      exec I (Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)).run st = some out ∧
      StoreContext tag dec N A b v ν status flag out.store ∧
      (∃ w, out.store.read tag 7 3 = some w ∧ dec tag w = γ) ∧
      γ = ν / μ * (1 + eγ) ∧ |eγ| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 < γ ∧
      ∀ q buf idx, (q ≠ tag ∨ buf ≠ 7 ∨ idx ≠ 3) →
        out.store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨wν, hν, hνdec⟩ := h.squaredResidual
  obtain ⟨wμ, hμread, hμdec⟩ := hμ
  obtain ⟨out, w, hrun, _, hshape, hread, hrel, hf⟩ :=
    hsem.exec_cg_division I tag st ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩ wν wμ hν hμread
      (by rw [hμdec]; exact ne_of_gt hμpos)
      ⟨9, by simp [h.shape, workspaceShape], by norm_num⟩
  rw [hνdec, hμdec] at hrel
  obtain ⟨eγ, heγ, hγ⟩ := hrel
  have hu := hsem.nonneg (p := tag) trivial
  have huε : u tag ≤ cgImplementationRoundoffBound N (u tag) := by
    have := four_mul_le_cgImplementationRoundoffBound hN hu
    linarith
  have heγ' := heγ.trans huε
  have hfactor : 0 < 1 + eγ := by linarith [(abs_le.mp heγ').1]
  refine ⟨out, dec tag w, eγ, hrun, ?_, ⟨w, hread, rfl⟩, hγ, heγ', ?_, hf⟩
  · apply h.preserve_frame hshape
    intro buf idx hcell
    apply hf tag buf idx
    change tag ≠ tag ∨ buf ≠ 7 ∨ idx ≠ 3
    rcases hcell with hb | ⟨rfl, hj⟩
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by rcases hj with rfl | rfl | rfl | rfl <;> norm_num))
  · rw [hγ]
    exact mul_pos (div_pos hνpos hμpos) hfactor

/-- The actual iterate axpy writes the decoded next iterate with its `CGRun.norm_ex_le`
bound, preserving the residual, direction, cache and all scalar words. -/
theorem exec_rounded_iterate_update (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag γ : ℝ) (h : StoreContext tag dec N A b v ν status flag st.store)
    (hγ : ∃ w, st.store.read tag 7 3 = some w ∧ dec tag w = γ)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (xnext : Fin N → ℝ),
      exec I (axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)).run st = some out ∧
      StoreContext tag dec N A b ⟨xnext, v.r, v.p⟩ ν status flag out.store ∧
      ‖WithLp.toLp 2 (v.x + γ • v.p - xnext)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.x‖ + |γ| * ‖WithLp.toLp 2 v.p‖) ∧
      ∀ q buf idx, buf ≠ 1 → out.store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨out, W, hrun, hshape, hread, herr, hframe⟩ :=
    hsem.exec_cg_axpy I tag st N ⟨7, 3⟩ 3 1 γ v.p v.x hγ h.direction h.iterate
      (by norm_num) (by norm_num) hN hsmall
  refine ⟨out, fun i => dec tag (W i), hrun, ?_, ?_, hframe⟩
  · apply h.replace_iterate hshape (fun i => dec tag (W i))
      (fun buf idx hb => hframe tag buf idx hb)
    intro i
    exact ⟨W i, hread i, rfl⟩
  · change ‖WithLp.toLp 2 (fun i : Fin N => v.x i + γ * v.p i - dec tag (W i))‖ ≤ _
    exact herr

/-- Exact negation of the actual step-length word followed by the actual residual axpy
supplies its `CGRun.norm_er_le` defect, without adding another scalar-rounding term. -/
theorem exec_rounded_residual_update (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag γ : ℝ) (sv : Fin N → ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store)
    (hγ : ∃ w, st.store.read tag 7 3 = some w ∧ dec tag w = γ)
    (hs : ∀ i : Fin N, ∃ w, st.store.read tag 6 i = some w ∧ dec tag w = sv i)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (rnext : Fin N → ℝ), exec I (do
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag dec N A b ⟨v.x, rnext, v.p⟩ ν status flag out.store ∧
      ‖WithLp.toLp 2 (v.r - γ • sv - rnext)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.r‖ + |γ| * ‖WithLp.toLp 2 sv‖) ∧
      ∀ q buf idx, buf ≠ 2 → (q ≠ tag ∨ buf ≠ 7 ∨ idx ≠ 5) →
        out.store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨wγ, hγread, hγdec⟩ := hγ
  obtain ⟨neg, hneg, hnegdec⟩ := hsem.neg tag wγ
  rw [hγdec] at hnegdec
  obtain ⟨store, hw, hrun, hshape, hread, hf⟩ := exec_scalar_un I tag st .neg
    ⟨7, 5⟩ ⟨7, 3⟩ wγ neg hγread hneg
    ⟨9, by simp [h.shape, workspaceShape], by norm_num⟩
  let mid : St P K C := { st with store := store, cnt := st.cnt + I.charge (.un tag .neg) }
  have hctx : StoreContext tag dec N A b v ν status flag mid.store :=
    h.preserve_scalar_write (by norm_num) (by norm_num) hw
  have hs' (i : Fin N) : ∃ w, mid.store.read tag 6 i = some w ∧ dec tag w = sv i := by
    obtain ⟨w, hread, hdec⟩ := hs i
    exact ⟨w, (hf tag 6 i (Or.inr (Or.inl (by norm_num)))).trans hread, hdec⟩
  obtain ⟨out, W, hout, hsh, hW, herr, hframe⟩ := hsem.exec_cg_axpy I tag mid N
    ⟨7, 5⟩ 6 2 (-γ) sv v.r ⟨neg, hread, hnegdec⟩ hs' hctx.residual
      (by norm_num) (by norm_num) hN hsmall
  refine ⟨out, fun i => dec tag (W i), ?_, ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩))
      (fun _ => rfl), hrun, Option.bind_some]
    exact hout
  · apply hctx.replace_residual hsh (fun i => dec tag (W i))
      (fun buf idx hb => hframe tag buf idx hb)
    intro i
    exact ⟨W i, hW i, rfl⟩
  · change ‖WithLp.toLp 2 (fun i : Fin N => v.r i - γ * sv i - dec tag (W i))‖ ≤ _
    simpa only [neg_mul, sub_eq_add_neg, abs_neg] using herr
  · intro q buf idx hb hidx
    exact (hframe q buf idx hb).trans (hf q buf idx hidx)

/-- The actual updated-residual dot supplies its next cached value and relative-error
witness, while the old cache remains available for the following direction quotient. -/
theorem exec_rounded_residual_pairing (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (νnext θnext : ℝ),
      exec I (dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)).run st = some out ∧
      StoreContext tag dec N A b v ν status flag out.store ∧
      (∃ w, out.store.read tag 7 1 = some w ∧ dec tag w = νnext) ∧
      νnext = ‖WithLp.toLp 2 v.r‖ ^ 2 * (1 + θnext) ∧
      |θnext| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 ≤ νnext ∧
      (νnext = 0 ↔ v.r = 0) ∧
      ∀ idx, idx ≠ 1 → out.store.read tag 7 idx = st.store.read tag 7 idx := by
  let rv : ℕ → ℝ := fun i => if hi : i < N then v.r ⟨i, hi⟩ else 0
  have hr (i : ℕ) (hi : i < N) :
      ∃ w, st.store.read tag 2 (0 + i) = some w ∧ dec tag w = rv i := by
    simpa only [zero_add, rv, dif_pos hi] using h.residual ⟨i, hi⟩
  obtain ⟨zero, _, _⟩ := h.zero
  obtain ⟨scratch, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape zero
    (show st.store.shape[7]? = some (tag, 9) by simp [h.shape, workspaceShape])
    (show 1 < 9 by norm_num)
  obtain ⟨out, w, θ, hrun, hwrite, heq, hθ, hnonneg, hzero⟩ := hsem.exec_cg_self_dot I tag
    hz st N ⟨7, 1⟩ 2 0 rv hN hsmall hr (by norm_num) ⟨zero, scratch, hw⟩
  have hrv : (fun i : Fin N => rv i) = v.r := by funext i; simp only [rv, dif_pos i.isLt]
  refine ⟨out, dec tag w, θ, hrun,
    h.preserve_scalar_write (by norm_num) (by norm_num) hwrite,
    ⟨w, Store.read_of_write_eq_some hwrite, rfl⟩, ?_, hθ, hnonneg, ?_, ?_⟩
  · simpa only [hrv] using heq
  · simpa only [hrv] using hzero
  · intro idx hi
    exact Store.read_of_write_eq_some_of_ne hwrite (Or.inr hi)

/-- The actual direction division uses the still-cached old residual denominator and the
newly paired numerator. Its `CGRun.δ_eq` error comes from this primitive division only. -/
theorem exec_rounded_direction_coefficient (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν νnext status flag : ℝ) (h : StoreContext tag dec N A b v ν status flag st.store)
    (hνnext : ∃ w, st.store.read tag 7 1 = some w ∧ dec tag w = νnext)
    (hνpos : 0 < ν) (hN : 0 < N) :
    ∃ (out : St P K C) (δ eδ : ℝ),
      exec I (Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)).run st = some out ∧
      StoreContext tag dec N A b v ν status flag out.store ∧
      (∃ w, out.store.read tag 7 4 = some w ∧ dec tag w = δ) ∧
      δ = νnext / ν * (1 + eδ) ∧ |eδ| ≤ cgImplementationRoundoffBound N (u tag) ∧
      ∀ q buf idx, (q ≠ tag ∨ buf ≠ 7 ∨ idx ≠ 4) →
        out.store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨wν, hν, hνdec⟩ := h.squaredResidual
  obtain ⟨wnext, hnextread, hnextdec⟩ := hνnext
  obtain ⟨out, w, hrun, _, hshape, hread, hrel, hf⟩ :=
    hsem.exec_cg_division I tag st ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩ wnext wν hnextread hν
      (by rw [hνdec]; exact ne_of_gt hνpos)
      ⟨9, by simp [h.shape, workspaceShape], by norm_num⟩
  rw [hnextdec, hνdec] at hrel
  obtain ⟨eδ, heδ, hδ⟩ := hrel
  have hu := hsem.nonneg (p := tag) trivial
  have huε : u tag ≤ cgImplementationRoundoffBound N (u tag) := by
    have := four_mul_le_cgImplementationRoundoffBound hN hu
    linarith
  refine ⟨out, dec tag w, eδ, hrun, ?_, ⟨w, hread, rfl⟩, hδ, heδ.trans huε, hf⟩
  apply h.preserve_frame hshape
  intro buf idx hcell
  apply hf tag buf idx
  change tag ≠ tag ∨ buf ≠ 7 ∨ idx ≠ 4
  rcases hcell with hb | ⟨rfl, hj⟩
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by rcases hj with rfl | rfl | rfl | rfl <;> norm_num))

/-- The actual inline two-operation direction update gives the `CGRun.norm_ep_le` defect
under the input-only implementation budget, and retains the old cache until its final copy. -/
theorem exec_rounded_direction_update (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag δ : ℝ) (h : StoreContext tag dec N A b v ν status flag st.store)
    (hδ : ∃ w, st.store.read tag 7 4 = some w ∧ dec tag w = δ)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (pnext : Fin N → ℝ),
      exec I (Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)).run st = some out ∧
      StoreContext tag dec N A b ⟨v.x, v.r, pnext⟩ ν status flag out.store ∧
      ‖WithLp.toLp 2 (v.r + δ • v.p - pnext)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.r‖ + |δ| * ‖WithLp.toLp 2 v.p‖) ∧
      ∀ idx, idx ≠ 2 → out.store.read tag 7 idx = st.store.read tag 7 idx := by
  have hu := hsem.nonneg (p := tag) trivial
  obtain ⟨_, hu2, _⟩ := cgImplementationRoundoffBound_kernel_bounds hN hu hsmall
  let pv : ℕ → ℝ := fun i => if hi : i < N then v.p ⟨i, hi⟩ else 0
  let rv : ℕ → ℝ := fun i => if hi : i < N then v.r ⟨i, hi⟩ else 0
  have hp (i : ℕ) (hi : i < N) :
      ∃ w, st.store.read tag 3 i = some w ∧ dec tag w = pv i := by
    simpa only [pv, dif_pos hi] using h.direction ⟨i, hi⟩
  have hr (i : ℕ) (hi : i < N) :
      ∃ w, st.store.read tag 2 i = some w ∧ dec tag w = rv i := by
    simpa only [rv, dif_pos hi] using h.residual ⟨i, hi⟩
  obtain ⟨zero, _, _⟩ := h.zero
  obtain ⟨scratch, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape zero
    (show st.store.shape[7]? = some (tag, 9) by simp [h.shape, workspaceShape])
    (show 2 < 9 by norm_num)
  have hdir := hsem.exec_cg_direction_update_norm_sub_le I tag st ⟨7, 4⟩ ⟨7, 2⟩
    3 2 (.const N) δ pv rv hu2 hδ hp hr (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ⟨zero, scratch, hw⟩
  simp only [IExp.eval_const] at hdir
  obtain ⟨out, W, hrun, hshape, _, hf, hread, herr⟩ := hdir
  have hframe (buf idx : ℕ) (hb : buf ≠ 3) (ht : buf ≠ 7 ∨ idx ≠ 2) :
      out.store.read tag buf idx = st.store.read tag buf idx :=
    hf tag buf idx (Or.inr (Or.inl hb)) (Or.inr ht)
  have hpv : (fun i : Fin N => pv i) = v.p := by funext i; simp only [pv, dif_pos i.isLt]
  have hrv : (fun i : Fin N => rv i) = v.r := by funext i; simp only [rv, dif_pos i.isLt]
  refine ⟨out, fun i => dec tag (W i), hrun, ?_, ?_, ?_⟩
  · apply h.replace_direction hshape (fun i => dec tag (W i)) hframe
    intro i
    exact ⟨W i, hread i, rfl⟩
  · have hfun : (fun i : Fin N => rv i + δ * pv i - dec tag (W i)) =
        v.r + δ • v.p - (fun i : Fin N => dec tag (W i)) := by rw [← hrv, ← hpv]; rfl
    rw [hfun, hpv, hrv] at herr
    exact herr.trans (mul_le_mul_of_nonneg_right
      (roundingFactor_two_le_cgImplementationRoundoffBound hN hu hsmall)
      (add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))))
  · intro idx hi
    exact hframe 7 idx (by norm_num) (Or.inr hi)

end NLAlib.CGImplementation
