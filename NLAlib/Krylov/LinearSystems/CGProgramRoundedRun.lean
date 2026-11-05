/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedBody

/-!
# Successful rounded execution prefixes and the existing CG run model

Cached residual errors are extracted from actual self-dot execution and word provenance.
The existing `CGRun` is used without a parallel arithmetic/run interface. A whole requested
horizon guarantee remains distinct from extraction of a successfully executed prefix.

## Main results

* `NLAlib.CGImplementation.initial_cache_of_self_dot_execution`: actual initial cache error.
* `NLAlib.CGImplementation.cgRun_one_of_initial_dot_execution`: actual first-step model.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation
open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}
  {mv : Builder P ι ℕ ℕ Unit}

/-- The initial cache error is derived from its actual self-dot run and the preserved word
origin at the active header. The initial-cache error bound is a conclusion, not a premise. -/
theorem initial_cache_of_self_dot_execution (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (predot cached header : St P K C) (N : ℕ) (b : Fin N → ℝ) (ν : ℝ)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hshape : predot.store.shape = workspaceShape tag N storedMatrix)
    (hr : ∀ i : Fin N, ∃ w, predot.store.read tag 2 i = some w ∧ dec tag w = b i)
    (hrun : exec I (dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)).run predot = some cached)
    (horigin : header.store.read tag 7 0 = cached.store.read tag 7 0)
    (hν : ∃ w, header.store.read tag 7 0 = some w ∧ dec tag w = ν) :
    ∃ θ, ν = ‖WithLp.toLp 2 b‖ ^ 2 * (1 + θ) ∧
      |θ| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 ≤ ν ∧ (ν = 0 ↔ b = 0) := by
  let rv : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  have hr' (i : ℕ) (hi : i < N) :
      ∃ w, predot.store.read tag 2 (0 + i) = some w ∧ dec tag w = rv i := by
    simpa only [rv, dif_pos hi, zero_add] using hr ⟨i, hi⟩
  obtain ⟨any, _, _⟩ := hr ⟨0, hN⟩
  obtain ⟨scratch, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape any
    (show predot.store.shape[7]? = some (tag, 9) by simp [hshape, workspaceShape])
    (show 0 < 9 by norm_num)
  obtain ⟨out, w, θ, hd, hwrite, heq, hθ, hnonneg, hzero⟩ := hsem.exec_cg_self_dot I tag
    hz predot N ⟨7, 0⟩ 2 0 rv hN hsmall hr' (by norm_num) ⟨any, scratch, hw⟩
  have hout : out = cached := Option.some.inj (hd.symm.trans hrun)
  have hread : cached.store.read tag 7 0 = some w := by
    rw [← hout]
    exact Store.read_of_write_eq_some hwrite
  obtain ⟨old, hold, hdec⟩ := hν
  have he : old = w := Option.some.inj (hold.symm.trans (horigin.trans hread))
  have hwdec : dec tag w = ν := by rw [← he]; exact hdec
  have hrv : (fun i : Fin N => rv i) = b := by funext i; simp only [rv, dif_pos i.isLt]
  rw [hwdec, hrv] at heq hzero
  exact ⟨θ, heq, hθ, hwdec ▸ hnonneg, hzero⟩

private theorem forall_lt_one {Q : ℕ → Prop} (h : Q 0) : ∀ j < 1, Q j := by
  intro j hj
  have : j = 0 := by omega
  simpa only [this] using h

private theorem forall_le_one {Q : ℕ → Prop} (h0 : Q 0) (h1 : Q 1) : ∀ j ≤ 1, Q j := by
  intro j hj
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · exact h0
  · exact h1

private noncomputable def oneStepRun (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ)
    (ε ν0 ν1 θ0 θ1 μ γ eγ δ eδ : ℝ) (hA : Aᵀ = A) (hε : 0 ≤ ε) (hεle : ε ≤ 1 / 100)
    (hν0 : ν0 = ‖WithLp.toLp 2 b‖ ^ 2 * (1 + θ0))
    (hν1 : ν1 = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θ1))
    (hθ0 : |θ0| ≤ ε) (hθ1 : |θ1| ≤ ε) (hνpos : 0 < ν0) (hμpos : 0 < μ)
    (hs : ‖WithLp.toLp 2 (A *ᵥ b - sv)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 b‖)
    (hμ : |b ⬝ᵥ sv - μ| ≤ ε * ‖WithLp.toLp 2 b‖ * ‖WithLp.toLp 2 sv‖)
    (hγ : γ = ν0 / μ * (1 + eγ)) (heγ : |eγ| ≤ ε)
    (hδ : δ = ν1 / ν0 * (1 + eδ)) (heδ : |eδ| ≤ ε)
    (hex : ‖WithLp.toLp 2 (γ • b - next.x)‖ ≤ ε * (|γ| * ‖WithLp.toLp 2 b‖))
    (her : ‖WithLp.toLp 2 (b - γ • sv - next.r)‖ ≤
      ε * (‖WithLp.toLp 2 b‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.r + δ • b - next.p)‖ ≤
      ε * (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 b‖)) : CGRun N 1 := by
  refine { A := A, b := b
           x := fun j => if j = 0 then 0 else next.x
           r := fun j => if j = 0 then b else next.r
           p := fun j => if j = 0 then b else next.p
           s := fun _ => sv
           ν := fun j => if j = 0 then ν0 else ν1
           μ := fun _ => μ
           γ := fun _ => γ
           δ := fun _ => δ
           es := fun _ => -(A *ᵥ b - sv)
           θ := fun j => if j = 0 then θ0 else θ1
           eμ := fun _ => -(b ⬝ᵥ sv - μ)
           eγ := fun _ => eγ
           ex := fun _ => -(γ • b - next.x)
           er := fun _ => -(b - γ • sv - next.r)
           eδ := fun _ => eδ
           ep := fun _ => -(next.r + δ • b - next.p)
           ε := ε, transpose_A := hA, ε_nonneg := hε, k_pos := by omega, ε_le := hεle
           x_zero := rfl, r_zero := rfl, p_zero := rfl
           ν_eq := forall_le_one hν0 hν1
           abs_θ_le := forall_le_one hθ0 hθ1
           ν_pos := forall_lt_one hνpos
           s_eq := forall_lt_one (by
             simp only [ite_true, neg_sub, ← add_sub_assoc, add_sub_cancel_left])
           norm_es_le := forall_lt_one (by
             simpa only [ite_true, WithLp.toLp_neg, norm_neg] using hs)
           μ_eq := forall_lt_one (by
             simp only [ite_true, neg_sub, ← add_sub_assoc, add_sub_cancel_left])
           abs_eμ_le := forall_lt_one (by simpa only [ite_true, abs_neg] using hμ)
           μ_pos := forall_lt_one hμpos
           γ_eq := forall_lt_one hγ
           abs_eγ_le := forall_lt_one heγ
           x_succ := forall_lt_one (by
             simp only [ite_true, if_neg Nat.one_ne_zero, zero_add, neg_sub,
               ← add_sub_assoc, add_sub_cancel_left])
           norm_ex_le := forall_lt_one (by
             simpa only [ite_true, WithLp.toLp_neg, norm_neg, WithLp.toLp_zero, norm_zero, zero_add]
               using hex)
           r_succ := forall_lt_one (by
             simp only [ite_true, if_neg Nat.one_ne_zero, neg_sub,
               ← add_sub_assoc, add_sub_cancel_left])
           norm_er_le := forall_lt_one (by
             simpa only [ite_true, WithLp.toLp_neg, norm_neg] using her)
           δ_eq := forall_lt_one hδ
           abs_eδ_le := forall_lt_one heδ
           p_succ := forall_lt_one (by
             simp only [ite_true, if_neg Nat.one_ne_zero, neg_sub,
               ← add_sub_assoc, add_sub_cancel_left])
           norm_ep_le := forall_lt_one (by
             simpa only [ite_true, if_neg Nat.one_ne_zero, WithLp.toLp_neg, norm_neg] using hep) }

/-- A nonzero first rounded step yields the EXISTING `CGRun N 1`, with actual physical
output cells and actual cached/scalar/product words. The initial error is extracted from its
self-dot execution origin, and every step defect is derived from executed instructions.
This is prefix extraction; it does not assert a whole requested-horizon no-breakdown result. -/
theorem cgRun_one_of_initial_dot_execution (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (predot cached st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (ν flag : ℝ)
    (h : StoreContext tag dec N A b ⟨0, b, b⟩ ν 0 flag
      st.store storedMatrix)
    (hpreShape : predot.store.shape = workspaceShape tag N storedMatrix)
    (hpreR : ∀ i : Fin N, ∃ w, predot.store.read tag 2 i = some w ∧ dec tag w = b i)
    (hinit : exec I (dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)).run predot = some cached)
    (horigin : st.store.read tag 7 0 = cached.store.read tag 7 0)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hprec : 3 * cgImplementationRoundoffBound N (u tag) * a' ≤ a) (hb : b ≠ 0)
    (hmv : IsMatvecRoutine I dec tag A (cgImplementationRoundoffBound N (u tag) *
      specNorm A) (fun store => if storedMatrix then HoldsDecoded store dec tag 5 0 A
      else True) 3 6 0 0 mv) :
    ∃ (prestate out : St P K C) (R : CGRun N 1),
      exec I (do
        mv
        dot tag ⟨7, 2⟩ 3 0 6 0 (.const N) : Builder P ι ℕ ℕ Unit).run
          { st with cnt := st.cnt + I.charge (.cmp tag) } = some prestate ∧
      exec I (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
      mv
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      (Builder.ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
      (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) : Builder P ι ℕ ℕ Unit)
      (pure ())).run st = some out ∧
      R.A = A ∧ R.b = b ∧ R.ε = cgImplementationRoundoffBound N (u tag) ∧ R.ν 0 = ν ∧
      StoreContext tag dec N A b ⟨R.x 1, R.r 1, R.p 1⟩ (R.ν 1)
        (if R.ν 1 = 0 then flag else 0) flag
        out.store storedMatrix ∧
      (∀ i : Fin N, ∃ w, prestate.store.read tag 6 i = some w ∧ dec tag w = R.s 0 i) ∧
      (∃ w, prestate.store.read tag 7 2 = some w ∧ dec tag w = R.μ 0) ∧
      (∃ w, out.store.read tag 7 3 = some w ∧ dec tag w = R.γ 0) ∧
      (∃ w, out.store.read tag 7 4 = some w ∧ dec tag w = R.δ 0) := by
  obtain ⟨θ0, hν0eq, hθ0, hνnonneg, hνzero⟩ := initial_cache_of_self_dot_execution I tag
    hsem hz predot cached st N b ν hN hsmall hpreShape hpreR hinit horigin h.squaredResidual
  have hνpos : 0 < ν := lt_of_le_of_ne hνnonneg (Ne.symm (fun he => hb (hνzero.mp he)))
  obtain ⟨prestate, out, next, sv, μ, ν1, θ1, γ, eγ, δ, eδ, hprefix, hrun, hctx,
      hs, hμ, hμpos, hes, heμ, hν1eq, hθ1, _, _, hγeq, heγ, _, hδeq, heδ,
      hex, her, hep, hγ, hδ⟩ := exec_rounded_positive_step (hmv := hmv) I tag hsem hz st N A b
        ⟨0, b, b⟩ ν flag h hνpos hN hsmall hA ha hspec hprec hb
  have hex' : ‖WithLp.toLp 2 (γ • b - next.x)‖ ≤
      cgImplementationRoundoffBound N (u tag) * (|γ| * ‖WithLp.toLp 2 b‖) := by
    simpa only [zero_add, WithLp.toLp_zero, norm_zero] using hex
  let R := oneStepRun N A b next sv (cgImplementationRoundoffBound N (u tag))
    ν ν1 θ0 θ1 μ γ eγ δ eδ hA
      (cgImplementationRoundoffBound_nonneg N (hsem.nonneg (p := tag) trivial)) hsmall
      hν0eq hν1eq hθ0 hθ1 hνpos hμpos hes heμ hγeq heγ hδeq heδ hex' her hep
  exact ⟨prestate, out, R, hprefix, hrun, rfl, rfl, rfl, rfl, hctx, hs, hμ, hγ, hδ⟩

end NLAlib.CGImplementation
