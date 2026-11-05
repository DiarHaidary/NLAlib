/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGOracleTargets
public import NLAlib.Krylov.LinearSystems.CGProgramLoop

/-!
# Exact oracle CG curvature execution

Actual oracle application writes the physical product workspace before the curvature dot.
The zero-capacity matrix reservation is a layout fact and requires no stored matrix entries.

## Main results

* `NLAlib.CGOracleImplementation.exec_exact_curvature`: actual oracle product and dot.
-/

@[expose] public section

namespace NLAlib.CGOracleImplementation

open Computation Computation.Builder CGImplementation
open scoped Matrix

variable {P ι : Type} [DecidableEq P]

/-- The actual one-column oracle call computes the product workspace, with a frame on every
other buffer. Its zero-dimensional instance is an empty legal block write. -/
theorem exec_exact_product (tag : P) (o : ι) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store false) :
    ∃ out, exec (exactInterp (fun _ => A) ξ) (.apply o tag 6 0 3 0 1) st = some out ∧
      StoreContext tag (fun _ x => x) N A b v ν status 1 out.store false ∧
      (∀ i : Fin N, out.store.read tag 6 i = some ((A *ᵥ v.p) i)) ∧
      out = { st with
        store := out.store
        cnt := st.cnt + (Finsupp.single (.load tag o) 1 +
          Finsupp.single (.matvec tag o) 1) } := by
  let W : Matrix (Fin N) (Fin 1) ℝ := fun i _ => v.p i
  obtain ⟨s, hw⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (s := st.store) (p := tag) (b := 6) (off := 0) (xs := flatten (A * W))
    (fun i hi => ⟨N, by simp [h.shape, workspaceShape], by simpa [size_flatten] using hi⟩)
  have hp (i : Fin N) (j : Fin 1) : st.store.read tag 3 (N * j + i) = some (W i j) := by
    obtain ⟨w, hw, rfl⟩ := h.direction i
    simpa only [Fin.fin_one_eq_zero j, Fin.val_zero, mul_zero, zero_add, W] using hw
  let out : St P ℝ (OpCount P ι) := { st with store := s, cnt := st.cnt +
    (Finsupp.single (.load tag o) 1 + Finsupp.single (.matvec tag o) 1) }
  refine ⟨out, ?_, ?_, ?_, rfl⟩
  · simpa only [IExp.eval_ofNat, one_nsmul, out] using
      exec_apply_exactInterp A ξ o tag 6 3 1 rfl st W (by norm_num) hp hw
  · apply h.preserve_frame (Store.shape_of_writeBlock_eq_some hw)
    intro buf idx hcell
    apply Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl ?_)
    rcases hcell with hb | ⟨rfl, _⟩ <;> omega
  · intro i
    have hr := Store.read_of_writeBlock_eq_some_of_lt hw
      (show (i : ℕ) < (flatten (A * W)).size by simp [size_flatten])
    have hf := getElem?_flatten (A * W) i (0 : Fin 1)
    have hvalue : s.read tag 6 i = some ((A * W) i 0) := by
      simpa only [zero_add, Fin.val_zero, mul_zero, add_zero] using hr.trans hf
    change s.read tag 6 i = some ((A *ᵥ v.p) i)
    have heq : (A * W) i 0 = (A *ᵥ v.p) i := rfl
    rwa [heq] at hvalue

/-- The oracle variant computes its own product and curvature pairing in actual program
order, preserving all persistent CG cells. No matrix entries are present in the store. -/
theorem exec_exact_curvature (tag : P) (o : ι) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v ν status 1 st.store false) :
    ∃ out, exec (exactInterp (fun _ => A) ξ) (do
      stmt (.apply o tag 6 0 3 0 1)
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b v ν status 1 out.store false ∧
      (∀ i : Fin N, out.store.read tag 6 i = some ((A *ᵥ v.p) i)) ∧
      out.store.read tag 7 2 = some (v.p ⬝ᵥ (A *ᵥ v.p)) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW := by
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  obtain ⟨mid, eprod, hctx, hv, state⟩ := exec_exact_product tag o N A ξ st b v ν status h
  have hp (i : Fin N) : mid.store.read tag 3 (0 + i) = some (v.p i) := by
    obtain ⟨w, hw, rfl⟩ := hctx.direction i
    simpa only [zero_add] using hw
  obtain ⟨scratch, hwrite⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : ℝ)
    (show mid.store.shape[7]? = some (tag, 9) by simp [hctx.shape, workspaceShape])
    (show 2 < 9 by norm_num)
  obtain ⟨out, hout, hshape, hμ, hframe, hpos, hcur, hcurW, _, _, _⟩ :=
    Computation.exec_dot_frame I rfl (fun _ => rfl) tag mid N ⟨7, 2⟩ 3 6 0 0 v.p (A *ᵥ v.p)
      hp (by simpa only [IExp.eval_zero, zero_add] using hv) (by norm_num) (by norm_num)
      ⟨0, scratch, hwrite⟩
  refine ⟨out, ?_, ?_, ?_, hμ, ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := stmt (.apply o tag 6 0 3 0 1)) (fun _ => rfl)]
    change (exec I (.seq (.apply o tag 6 0 3 0 1) .skip) st).bind _ = _
    rw [exec_seq_skip, eprod, Option.bind_some]
    exact hout
  · apply hctx.preserve_frame hshape
    intro buf idx hcell
    apply hframe tag buf idx
    change buf ≠ 7 ∨ idx ≠ 2
    rcases hcell with hb | ⟨rfl, hj⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by rcases hj with rfl | rfl | rfl | rfl <;> norm_num)
  · intro i
    exact (hframe tag 6 i (Or.inl (by norm_num))).trans (hv i)
  · exact hpos.trans (by simpa only using congrArg St.pos state)
  · exact hcur.trans (by simpa only using congrArg St.cur state)
  · exact hcurW.trans (by simpa only using congrArg St.curW state)

end NLAlib.CGOracleImplementation
