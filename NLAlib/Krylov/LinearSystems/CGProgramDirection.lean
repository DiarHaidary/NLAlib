/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RoundingErrors

/-!
# The inline direction update of the stored CG program

This supporting execution proof proves execution of the actual two-operation loop in
`CGProgramTree.lean`: multiply the old direction by the coefficient in a scratch cell,
then add the residual into the direction cell. The residual is never overwritten, and no
extra multiplication by one is inserted. It introduces no separate algorithm program.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_cg_direction_update`: actual successful loop execution,
  componentwise rounding traces, exact charged operation counts, unchanged usage fields,
  and store preservation outside the direction and scratch.
* `NLAlib.CGImplementation.exec_cg_direction_update_of_sem_eq_exactSem`: exact direction output.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  (I : Interp P ι K C) (tag : P) {dec : P → K → ℝ} {u : P → ℝ}

private theorem read_of_write_of_outside {s s' : Store P K} {p q : P}
    {b i b' i' : ℕ} {v : K} (hw : s.write p b i v = some s')
    (hne : q ≠ p ∨ b' ≠ b ∨ i' ≠ i) : s'.read q b' i' = s.read q b' i' := by
  rcases hne with hq | hcell
  · exact Store.read_of_write_eq_some_of_ne_tag hw hq
  · exact Store.read_of_write_eq_some_of_ne hw hcell

/-- A single direction component, retaining the actual writes and their error relations. -/
private theorem exec_cg_direction_component
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (st : St P K C) (coeff tmp : Cell ℕ ℕ) (p r i : ℕ)
    {wc wp wr : K} (hc : st.store.read tag coeff.buf coeff.idx.eval = some wc)
    (hp : st.store.read tag p i = some wp) (hr : st.store.read tag r i = some wr)
    (htr : tmp.buf ≠ r)
    (ht : ∃ w s, st.store.write tag tmp.buf tmp.idx.eval w = some s) :
    ∃ st' w v s₁,
      exec I (.seq (.instr (.bin tag .mul tmp coeff ⟨p, .const i⟩))
        (.seq (.instr (.bin tag .add ⟨p, .const i⟩ ⟨r, .const i⟩ tmp)) .skip)) st =
          some st' ∧
      st.store.write tag tmp.buf tmp.idx.eval v = some s₁ ∧
      s₁.write tag p i w = some st'.store ∧
      st' = { st with
        store := st'.store
        cnt := (st.cnt + I.charge (.bin tag .mul)) + I.charge (.bin tag .add) } ∧
      RelErr (u tag) (dec tag wc * dec tag wp) (dec tag v) ∧
      RelErr (u tag) (dec tag wr + dec tag v) (dec tag w) := by
  obtain ⟨v, hv⟩ := h.bin_ok tag .mul wc wp trivial (fun h => nomatch h) trivial
  obtain ⟨old, s, hs⟩ := ht
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_write_eq_some hs v
  have hr₁ : s₁.read tag r i = some wr := by
    rw [Store.read_of_write_eq_some_of_ne h₁ (Or.inl htr.symm)]
    exact hr
  obtain ⟨w, hw⟩ := h.bin_ok tag .add wr v trivial (fun h => nomatch h) trivial
  obtain ⟨s₀, h₀⟩ := Store.exists_write_eq_some_of_read_eq_some (v := w) hp
  obtain ⟨s₂, h₂⟩ := Store.exists_write_eq_some_of_shape_eq
    (Store.shape_of_write_eq_some h₁) h₀ w
  refine ⟨{ st with
      store := s₂
      cnt := (st.cnt + I.charge (.bin tag .mul)) + I.charge (.bin tag .add) },
    w, v, s₁, ?_, h₁, h₂, rfl, h.bin_err tag .mul wc wp v trivial hv,
    h.bin_err tag .add wr v w trivial hw⟩
  exact (exec_seq_instr_bin I hc hp hv h₁).trans
    ((exec_seq_instr_bin I hr₁ (Store.read_of_write_eq_some h₁) hw h₂).trans (exec_skip I _))

/-- The stored CG direction update succeeds under the scalar relative-error contract.
Only direction entries and the scratch cell change. The returned errors are derived from
executed multiplication and addition, and are not premises about their desired outputs.
The count increases by exactly the dimension times the charge of one multiplication followed
by one addition. All non-store, non-count state fields remain unchanged. -/
theorem IsRelErrSem.exec_cg_direction_update
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (st : St P K C) (coeff tmp : Cell ℕ ℕ) (p r : ℕ) (n : IExp ℕ)
    (av : ℝ) (pv rv : ℕ → ℝ)
    (hc : ∃ w, st.store.read tag coeff.buf coeff.idx.eval = some w ∧ dec tag w = av)
    (hp : ∀ i < n.eval, ∃ w, st.store.read tag p i = some w ∧ dec tag w = pv i)
    (hr : ∀ i < n.eval, ∃ w, st.store.read tag r i = some w ∧ dec tag w = rv i)
    (hpr : p ≠ r) (htp : tmp.buf ≠ p) (htr : tmp.buf ≠ r) (hcp : coeff.buf ≠ p)
    (htc : tmp.buf = coeff.buf → tmp.idx.eval ≠ coeff.idx.eval)
    (ht : ∃ w s, st.store.write tag tmp.buf tmp.idx.eval w = some s) :
    ∃ st', exec I (forRange n fun i => do
        ins (.bin tag .mul tmp coeff ⟨p, .var i⟩)
        ins (.bin tag .add ⟨p, .var i⟩ ⟨r, .var i⟩ tmp)).run st = some st' ∧
      st'.store.shape = st.store.shape ∧
      st' = { st with
        store := st'.store
        cnt := st.cnt + n.eval • (I.charge (.bin tag .mul) + I.charge (.bin tag .add)) } ∧
      (∀ q b j, (q ≠ tag ∨ b ≠ p ∨ n.eval ≤ j) →
        (q ≠ tag ∨ b ≠ tmp.buf ∨ j ≠ tmp.idx.eval) →
        st'.store.read q b j = st.store.read q b j) ∧
      ∀ i < n.eval, ∃ w v, st'.store.read tag p i = some w ∧
        RelErr (u tag) (av * pv i) v ∧ RelErr (u tag) (rv i + v) (dec tag w) := by
  classical
  obtain ⟨wc, hc, hvc⟩ := hc
  let R (k : ℕ) (σ : St P K C) : Prop :=
    σ.store.shape = st.store.shape ∧
    σ = { st with
      store := σ.store
      cnt := st.cnt + k • (I.charge (.bin tag .mul) + I.charge (.bin tag .add)) } ∧
    (∀ q b j, (q ≠ tag ∨ b ≠ p ∨ k ≤ j) →
      (q ≠ tag ∨ b ≠ tmp.buf ∨ j ≠ tmp.idx.eval) →
      σ.store.read q b j = st.store.read q b j) ∧
    ∀ i < k, ∃ w v, σ.store.read tag p i = some w ∧
      RelErr (u tag) (av * pv i) v ∧ RelErr (u tag) (rv i + v) (dec tag w)
  have h0 : R 0 st := ⟨rfl, by simp, fun _ _ _ _ _ => rfl, fun i hi => by omega⟩
  have hstep : ∀ i < n.eval, ∀ σ, R i σ → ∃ σ',
      exec I (.seq (.instr (.bin tag .mul tmp coeff ⟨p, .const i⟩))
        (.seq (.instr (.bin tag .add ⟨p, .const i⟩ ⟨r, .const i⟩ tmp)) .skip)) σ =
          some σ' ∧ R (i + 1) σ' := by
    intro i hi σ ⟨hshape, hstate, hframe, hout⟩
    obtain ⟨wp, hp, hvp⟩ := hp i hi
    obtain ⟨wr, hr, hvr⟩ := hr i hi
    have hc' : σ.store.read tag coeff.buf coeff.idx.eval = some wc := by
      rw [hframe tag coeff.buf coeff.idx.eval (Or.inr (Or.inl hcp)) ?_, hc]
      by_cases hb : coeff.buf = tmp.buf
      · exact Or.inr (Or.inr (Ne.symm (htc hb.symm)))
      · exact Or.inr (Or.inl hb)
    have hp' : σ.store.read tag p i = some wp := by
      rw [hframe tag p i (Or.inr (Or.inr le_rfl)) (Or.inr (Or.inl htp.symm)), hp]
    have hr' : σ.store.read tag r i = some wr := by
      rw [hframe tag r i (Or.inr (Or.inl hpr.symm)) (Or.inr (Or.inl htr.symm)), hr]
    obtain ⟨old, s, hs⟩ := ht
    have ht' : ∃ w s, σ.store.write tag tmp.buf tmp.idx.eval w = some s := by
      obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_shape_eq hshape hs old
      exact ⟨old, s', hs'⟩
    obtain ⟨σ', w, v, s₁, hrun, h₁, h₂, hstate', hmul, hadd⟩ :=
      exec_cg_direction_component I tag h σ coeff tmp p r i hc' hp' hr' htr ht'
    refine ⟨σ', hrun, (Store.shape_of_write_eq_some h₂).trans
      ((Store.shape_of_write_eq_some h₁).trans hshape), ?_, ?_, ?_⟩
    · calc
        σ' = { σ with
          store := σ'.store
          cnt := (σ.cnt + I.charge (.bin tag .mul)) + I.charge (.bin tag .add) } := hstate'
        _ = _ := by rw [hstate]; simp only [succ_nsmul, add_assoc]
    · intro q b j hj htj
      have hne : q ≠ tag ∨ b ≠ p ∨ j ≠ i := by
        rcases hj with hq | hb | hj
        · exact Or.inl hq
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr (by omega))
      rw [read_of_write_of_outside h₂ hne,
        read_of_write_of_outside h₁ htj]
      apply hframe q b j _ htj
      rcases hj with hq | hb | hj
      · exact Or.inl hq
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (by omega))
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨wj, vj, hwj, hmj, haj⟩ := hout j hj
        refine ⟨wj, vj, ?_, hmj, haj⟩
        rw [Store.read_of_write_eq_some_of_ne h₂ (Or.inr (by omega)),
          Store.read_of_write_eq_some_of_ne h₁ (Or.inl htp.symm)]
        exact hwj
      · exact ⟨w, dec tag v, Store.read_of_write_eq_some h₂,
          by simpa [hvc, hvp] using hmul, by simpa [hvr] using hadd⟩
  obtain ⟨st', hrun, hR⟩ := exists_exec_loop_eq_some_of_forall I R h0 hstep
  refine ⟨st', ?_, hR⟩
  change exec I (.seq (.loop n _) .skip) st = some st'
  rw [exec_seq_skip]
  exact hrun

end NLAlib.Computation

namespace NLAlib.CGImplementation

open Computation

/-- The actual inline direction update computes the exact CG direction under exact semantics.
It preserves the residual and every other cell outside the direction and scratch, and has
two arithmetic operations per component with no additional memory. -/
theorem exec_cg_direction_update_of_sem_eq_exactSem
    {P ι : Type} [DecidableEq P] (I : Interp P ι ℝ (OpCount P ι)) (tag : P)
    (hsem : I.sem = exactSem)
    (st : St P ℝ (OpCount P ι)) (coeff tmp : Cell ℕ ℕ) (p r : ℕ) (n : IExp ℕ)
    (av : ℝ) (pv rv : ℕ → ℝ)
    (hc : st.store.read tag coeff.buf coeff.idx.eval = some av)
    (hp : ∀ i < n.eval, st.store.read tag p i = some (pv i))
    (hr : ∀ i < n.eval, st.store.read tag r i = some (rv i))
    (hpr : p ≠ r) (htp : tmp.buf ≠ p) (htr : tmp.buf ≠ r) (hcp : coeff.buf ≠ p)
    (htc : tmp.buf = coeff.buf → tmp.idx.eval ≠ coeff.idx.eval)
    (ht : ∃ w s, st.store.write tag tmp.buf tmp.idx.eval w = some s) :
    ∃ st', exec I (Builder.forRange n fun i => do
        Builder.ins (.bin tag .mul tmp coeff ⟨p, .var i⟩)
        Builder.ins (.bin tag .add ⟨p, .var i⟩ ⟨r, .var i⟩ tmp)).run st = some st' ∧
      st'.store.shape = st.store.shape ∧
      st' = { st with
        store := st'.store
        cnt := st.cnt + n.eval • (I.charge (.bin tag .mul) + I.charge (.bin tag .add)) } ∧
      (∀ q b j, (q ≠ tag ∨ b ≠ p ∨ n.eval ≤ j) →
        (q ≠ tag ∨ b ≠ tmp.buf ∨ j ≠ tmp.idx.eval) →
        st'.store.read q b j = st.store.read q b j) ∧
      ∀ i < n.eval, st'.store.read tag p i = some (rv i + av * pv i) := by
  have h : IsRelErrSem (fun _ => 0) (fun _ x => x) (fun _ _ => True) I.sem := by
    rw [hsem]
    exact isRelErrSem_exactSem
  obtain ⟨st', hrun, hshape, hstate, hframe, hout⟩ :=
    IsRelErrSem.exec_cg_direction_update I tag h st coeff tmp p r n av pv rv
      ⟨av, hc, rfl⟩ (fun i hi => ⟨pv i, hp i hi, rfl⟩)
      (fun i hi => ⟨rv i, hr i hi, rfl⟩) hpr htp htr hcp htc ht
  refine ⟨st', hrun, hshape, hstate, hframe, fun i hi => ?_⟩
  obtain ⟨w, v, hw, hmul, hadd⟩ := hout i hi
  obtain ⟨δ, hδ, hv⟩ := hmul
  obtain ⟨η, hη, he⟩ := hadd
  have hδ0 : δ = 0 := abs_eq_zero.mp (le_antisymm hδ (abs_nonneg _))
  have hη0 : η = 0 := abs_eq_zero.mp (le_antisymm hη (abs_nonneg _))
  have hv' : v = av * pv i := by simpa only [hδ0, add_zero, mul_one] using hv
  have he' : w = rv i + v := by simpa only [hη0, add_zero, mul_one] using he
  simpa only [he', hv'] using hw

end NLAlib.CGImplementation
