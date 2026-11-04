/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedStop

/-!
# Composed actual rounded CG body phases

The fixed instruction/kernel sequence is composed from actual executions. All local errors
come from the primitive contract and the explicit implementation budget. This is supporting
successful-prefix extraction into the existing `CGRun`, not a new arithmetic/run interface.

## Main results

* `NLAlib.CGImplementation.exec_rounded_primal`: the actual iterate/residual phase.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation
open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ}

/-- The actual division, iterate axpy, negation and residual axpy return physical next x/r
and their CG defects, with the actual decoded step length retained in scalar cell 3. -/
theorem exec_rounded_primal (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag μ : ℝ) (sv : Fin N → ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store)
    (hμ : ∃ w, st.store.read tag 7 2 = some w ∧ dec tag w = μ)
    (hs : ∀ i : Fin N, ∃ w, st.store.read tag 6 i = some w ∧ dec tag w = sv i)
    (hνpos : 0 < ν) (hμpos : 0 < μ) (hN : 0 < N)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (γ eγ : ℝ) (xnext rnext : Fin N → ℝ), exec I (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag dec N A b ⟨xnext, rnext, v.p⟩ ν status flag out.store ∧
      γ = ν / μ * (1 + eγ) ∧ |eγ| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 < γ ∧
      ‖WithLp.toLp 2 (v.x + γ • v.p - xnext)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.x‖ + |γ| * ‖WithLp.toLp 2 v.p‖) ∧
      ‖WithLp.toLp 2 (v.r - γ • sv - rnext)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.r‖ + |γ| * ‖WithLp.toLp 2 sv‖) ∧
      (∃ w, out.store.read tag 7 3 = some w ∧ dec tag w = γ) := by
  obtain ⟨sg, γ, eγ, hg, hcg, hγ, hgeq, hge, hgpos, hfg⟩ := exec_rounded_step_length I tag
    hsem st N A b v ν status flag μ h hμ hνpos hμpos hN hsmall
  obtain ⟨sx, xnext, hx, hcx, hex, hfx⟩ := exec_rounded_iterate_update I tag hsem sg N A b v
    ν status flag γ hcg hγ hN hsmall
  have hγx : ∃ w, sx.store.read tag 7 3 = some w ∧ dec tag w = γ := by
    obtain ⟨w, hw, hdec⟩ := hγ
    exact ⟨w, (hfx tag 7 3 (by norm_num)).trans hw, hdec⟩
  have hsx (i : Fin N) : ∃ w, sx.store.read tag 6 i = some w ∧ dec tag w = sv i := by
    obtain ⟨w, hw, hdec⟩ := hs i
    exact ⟨w, (hfx tag 6 i (by norm_num)).trans
      ((hfg tag 6 i (Or.inr (Or.inl (by norm_num)))).trans hw), hdec⟩
  obtain ⟨out, rnext, hr, hcr, her, hfr⟩ := exec_rounded_residual_update I tag hsem sx N A b
    ⟨xnext, v.r, v.p⟩ ν status flag γ sv hcx hγx hsx hN hsmall
  refine ⟨out, γ, eγ, xnext, rnext, ?_, hcr, hgeq, hge, hgpos, hex, her, ?_⟩
  · rw [exec_run_bind I (b := Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩))
      (fun _ => rfl), hg, Option.bind_some,
      exec_run_bind I (b := axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N))
      (fun _ => rfl), hx, Option.bind_some]
    exact hr
  · obtain ⟨w, hw, hdec⟩ := hγx
    exact ⟨w, (hfr tag 7 3 (by norm_num) (Or.inr (Or.inr (by norm_num)))).trans hw, hdec⟩

/-- The actual residual pairing, quotient, inline direction update and final cache/stop
operations complete the new state, retaining the next coefficient and previous step length. -/
theorem exec_rounded_search (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store) (hνpos : 0 < ν)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (νnext θnext δ eδ : ℝ) (pnext : Fin N → ℝ), exec I (do
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()) : Builder P ι ℕ ℕ Unit).run st =
      some out ∧ StoreContext tag dec N A b ⟨v.x, v.r, pnext⟩ νnext
        (if νnext = 0 then flag else status) flag out.store ∧
      νnext = ‖WithLp.toLp 2 v.r‖ ^ 2 * (1 + θnext) ∧
      |θnext| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 ≤ νnext ∧
      (νnext = 0 ↔ v.r = 0) ∧ δ = νnext / ν * (1 + eδ) ∧
      |eδ| ≤ cgImplementationRoundoffBound N (u tag) ∧
      ‖WithLp.toLp 2 (v.r + δ • v.p - pnext)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.r‖ + |δ| * ‖WithLp.toLp 2 v.p‖) ∧
      (∃ w, out.store.read tag 7 4 = some w ∧ dec tag w = δ) ∧
      out.store.read tag 7 3 = st.store.read tag 7 3 := by
  obtain ⟨sn, νnext, θnext, hn, hcn, hνnext, hneq, hθ, hnonneg, hzero, hnf⟩ :=
    exec_rounded_residual_pairing I tag hsem hz st N A b v ν status flag h hN hsmall
  obtain ⟨sd, δ, eδ, hd, hcd, hδ, hdeq, hde, hdf⟩ :=
    exec_rounded_direction_coefficient I tag hsem sn N A b v ν νnext status flag hcn
      hνnext hνpos hN
  have hνd : ∃ w, sd.store.read tag 7 1 = some w ∧ dec tag w = νnext := by
    obtain ⟨w, hw, hdec⟩ := hνnext
    exact ⟨w, (hdf tag 7 1 (Or.inr (Or.inr (by norm_num)))).trans hw, hdec⟩
  obtain ⟨sp, pnext, hp, hcp, hep, hpf⟩ := exec_rounded_direction_update I tag hsem sd N A b
    v ν status flag δ hcd hδ hN hsmall
  have hνp : ∃ w, sp.store.read tag 7 1 = some w ∧ dec tag w = νnext := by
    obtain ⟨w, hw, hdec⟩ := hνd
    exact ⟨w, (hpf 1 (by norm_num)).trans hw, hdec⟩
  obtain ⟨out, hout, hctx, hf⟩ := exec_rounded_cache_and_stop I tag hsem sp N A b
    ⟨v.x, v.r, pnext⟩ ν νnext status flag hcp hνp
  refine ⟨out, νnext, θnext, δ, eδ, pnext, ?_, hctx, hneq, hθ, hnonneg, hzero,
    hdeq, hde, hep, ?_, ?_⟩
  · rw [exec_run_bind I (b := dot tag ⟨7, 1⟩ 2 0 2 0 (.const N))
      (fun _ => rfl), hn, Option.bind_some,
      exec_run_bind I (b := Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩))
      (fun _ => rfl), hd, Option.bind_some,
      exec_run_bind I (b := Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)) (fun _ => rfl),
      hp, Option.bind_some]
    exact hout
  · obtain ⟨w, hw, hdec⟩ := hδ
    exact ⟨w, (hf 4 (by norm_num)).trans ((hpf 4 (by norm_num)).trans hw), hdec⟩
  · exact (hf 3 (by norm_num)).trans ((hpf 3 (by norm_num)).trans
      ((hdf tag 7 3 (Or.inr (Or.inr (by norm_num)))).trans (hnf 3 (by norm_num))))

/-- The entire fixed rounded positive-curvature body computes actual next-state cells and
all scalar/vector local defects needed by `CGRun`. Positive ν/μ are actual branch facts;
this supporting theorem does not assert input-only success through a requested horizon. -/
theorem exec_rounded_positive_body (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (v : CGState ℝ (Fin N)) (ν status flag μ : ℝ) (sv : Fin N → ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store)
    (hμ : ∃ w, st.store.read tag 7 2 = some w ∧ dec tag w = μ)
    (hs : ∀ i : Fin N, ∃ w, st.store.read tag 6 i = some w ∧ dec tag w = sv i)
    (hνpos : 0 < ν) (hμpos : 0 < μ) (hN : 0 < N)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (next : CGState ℝ (Fin N)) (νnext θnext γ eγ δ eδ : ℝ), exec I (do
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
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()) : Builder P ι ℕ ℕ Unit).run st =
      some out ∧ StoreContext tag dec N A b next νnext
        (if νnext = 0 then flag else status) flag out.store ∧
      νnext = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θnext) ∧
      |θnext| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 ≤ νnext ∧
      (νnext = 0 ↔ next.r = 0) ∧ γ = ν / μ * (1 + eγ) ∧
      |eγ| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 < γ ∧
      δ = νnext / ν * (1 + eδ) ∧ |eδ| ≤ cgImplementationRoundoffBound N (u tag) ∧
      ‖WithLp.toLp 2 (v.x + γ • v.p - next.x)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.x‖ + |γ| * ‖WithLp.toLp 2 v.p‖) ∧
      ‖WithLp.toLp 2 (v.r - γ • sv - next.r)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.r‖ + |γ| * ‖WithLp.toLp 2 sv‖) ∧
      ‖WithLp.toLp 2 (next.r + δ • v.p - next.p)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 v.p‖) ∧
      (∃ w, out.store.read tag 7 3 = some w ∧ dec tag w = γ) ∧
      (∃ w, out.store.read tag 7 4 = some w ∧ dec tag w = δ) := by
  obtain ⟨mid, γ, eγ, xnext, rnext, hrun, hctx, hγeq, heγ, hγpos, hex, her, hγ⟩ :=
    exec_rounded_primal I tag hsem st N A b v ν status flag μ sv h hμ hs
      hνpos hμpos hN hsmall
  obtain ⟨out, νnext, θnext, δ, eδ, pnext, hout, hctx', hνeq, hθ, hnonneg, hzero,
      hδeq, heδ, hep, hδ, hγframe⟩ := exec_rounded_search I tag hsem hz mid N A b
        ⟨xnext, rnext, v.p⟩ ν status flag hctx hνpos hN hsmall
  have hcompose : ExecutionComposable I (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl))))
  refine ⟨out, ⟨xnext, rnext, pnext⟩, νnext, θnext, γ, eγ, δ, eδ, ?_, hctx',
    hνeq, hθ, hnonneg, hzero, hγeq, heγ, hγpos, hδeq, heδ, hex, her, hep, ?_, hδ⟩
  · change exec I ((do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)) >>= fun _ => _).run st = _
    rw [hcompose, hrun, Option.bind_some]
    exact hout
  · obtain ⟨w, hw, hdec⟩ := hγ
    exact ⟨w, hγframe.trans hw, hdec⟩

/-- The actual matvec and curvature dot expose their decoded local defects together.
The dot error is measured against the computed product, not charged the matvec error twice. -/
theorem exec_rounded_curvature_prefix (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K C) (sv : Fin N → ℝ) (μ : ℝ), exec I (do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag dec N A b v ν status flag out.store ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 6 i = some w ∧ dec tag w = sv i) ∧
      (∃ w, out.store.read tag 7 2 = some w ∧ dec tag w = μ) ∧
      ‖WithLp.toLp 2 (A *ᵥ v.p - sv)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        specNorm A * ‖WithLp.toLp 2 v.p‖ ∧
      |v.p ⬝ᵥ sv - μ| ≤ cgImplementationRoundoffBound N (u tag) *
        ‖WithLp.toLp 2 v.p‖ * ‖WithLp.toLp 2 sv‖ := by
  obtain ⟨mid, sv, hrun, hctx, hs, hes⟩ := exec_rounded_matvec I tag hsem hz st N A b v
    ν status flag h hN hsmall
  obtain ⟨out, μ, hout, hctx', hμ, hs', heμ⟩ := exec_rounded_curvature I tag hsem hz mid N
    A b v ν status flag sv hctx hs hN hsmall
  refine ⟨out, sv, μ, ?_, hctx', hs', hμ, hes, heμ⟩
  rw [exec_run_bind I (b := gemv tag (.const N) (.const N) 5 0 3 0 6 0)
    (fun _ => rfl), hrun, Option.bind_some]
  exact hout

/-- The actual computed curvature is positive under the explicit spectral/precision window
and a nonzero decoded direction. The local defects used here are derived from execution. -/
theorem exec_rounded_curvature_prefix_pos (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (h : StoreContext tag dec N A b v ν status flag st.store)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hprec : 3 * cgImplementationRoundoffBound N (u tag) * a' ≤ a) (hp : v.p ≠ 0) :
    ∃ (out : St P K C) (sv : Fin N → ℝ) (μ : ℝ), exec I (do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag dec N A b v ν status flag out.store ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 6 i = some w ∧ dec tag w = sv i) ∧
      (∃ w, out.store.read tag 7 2 = some w ∧ dec tag w = μ) ∧ 0 < μ ∧
      ‖WithLp.toLp 2 (A *ᵥ v.p - sv)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        specNorm A * ‖WithLp.toLp 2 v.p‖ ∧
      |v.p ⬝ᵥ sv - μ| ≤ cgImplementationRoundoffBound N (u tag) *
        ‖WithLp.toLp 2 v.p‖ * ‖WithLp.toLp 2 sv‖ := by
  obtain ⟨out, sv, μ, hrun, hctx, hs, hμ, hes, heμ⟩ :=
    exec_rounded_curvature_prefix I tag hsem hz st N A b v ν status flag h hN hsmall
  have heq : A *ᵥ v.p + (sv - A *ᵥ v.p) = sv := by abel
  have hes' : ‖WithLp.toLp 2 (sv - A *ᵥ v.p)‖ ≤
      cgImplementationRoundoffBound N (u tag) * specNorm A * ‖WithLp.toLp 2 v.p‖ := by
    rw [WithLp.toLp_sub, norm_sub_rev, ← WithLp.toLp_sub]
    exact hes
  have heμ' : |μ - v.p ⬝ᵥ sv| ≤ cgImplementationRoundoffBound N (u tag) *
      ‖WithLp.toLp 2 v.p‖ * ‖WithLp.toLp 2 (A *ᵥ v.p + (sv - A *ᵥ v.p))‖ := by
    rw [heq, abs_sub_comm]
    exact heμ
  have hpos := dotProduct_add_pos_of_spectrum_subset_Icc hA ha hspec
    (cgImplementationRoundoffBound_nonneg N (hsem.nonneg (p := tag) trivial)) hprec hp hes' heμ'
  rw [heq] at hpos
  exact ⟨out, sv, μ, hrun, hctx, hs, hμ, by linarith, hes, heμ⟩

private theorem cmp_status_zero (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν flag : ℝ)
    (h : StoreContext tag dec N A b v ν 0 flag st.store) :
    cmpStep I tag .eq ⟨4, 0⟩ ⟨7, 6⟩ st =
      some (true, { st with cnt := st.cnt + I.charge (.cmp tag) }) := by
  obtain ⟨ws, hs, hds⟩ := h.statusValue
  obtain ⟨wz, hz, hdz⟩ := h.zero
  have hc : I.sem.cmp tag .eq ws wz = some true := by
    simpa only [hds, hdz, decide_true] using hsem.cmp_eq tag ws wz
  simp only [cmpStep, IExp.eval_ofNat, hs, hz, Option.bind_some, hc, Option.map_some]

private theorem cmp_curvature_positive (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag μ : ℝ) (h : StoreContext tag dec N A b v ν status flag st.store)
    (hμ : ∃ w, st.store.read tag 7 2 = some w ∧ dec tag w = μ) (hμpos : 0 < μ) :
    cmpStep I tag .lt ⟨7, 6⟩ ⟨7, 2⟩ st =
      some (true, { st with cnt := st.cnt + I.charge (.cmp tag) }) := by
  obtain ⟨wm, hm, hdm⟩ := hμ
  obtain ⟨wz, hz, hdz⟩ := h.zero
  have hc : I.sem.cmp tag .lt wz wm = some true := by
    simpa only [hdm, hdz, hμpos, decide_true] using hsem.cmp_lt tag wz wm
  simp only [cmpStep, IExp.eval_ofNat, hz, hm, Option.bind_some, hc, Option.map_some]

/-- One full actual requested iteration, under explicit spectral/precision inputs and a
nonzero decoded direction, supplies its existing-CGRun local data. The positive curvature is
derived from the executed prefix, not assumed as a desired local property. -/
theorem exec_rounded_positive_step (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (v : CGState ℝ (Fin N)) (ν flag : ℝ)
    (h : StoreContext tag dec N A b v ν 0 flag st.store) (hνpos : 0 < ν)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hprec : 3 * cgImplementationRoundoffBound N (u tag) * a' ≤ a) (hp : v.p ≠ 0) :
    ∃ (prestate out : St P K C) (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ)
        (μ νnext θnext γ eγ δ eδ : ℝ),
      exec I (do
        gemv tag (.const N) (.const N) 5 0 3 0 6 0
        dot tag ⟨7, 2⟩ 3 0 6 0 (.const N) : Builder P ι ℕ ℕ Unit).run
          { st with cnt := st.cnt + I.charge (.cmp tag) } = some prestate ∧
      exec I (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
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
      StoreContext tag dec N A b next νnext (if νnext = 0 then flag else 0) flag out.store ∧
      (∀ i : Fin N, ∃ w, prestate.store.read tag 6 i = some w ∧ dec tag w = sv i) ∧
      (∃ w, prestate.store.read tag 7 2 = some w ∧ dec tag w = μ) ∧ 0 < μ ∧
      ‖WithLp.toLp 2 (A *ᵥ v.p - sv)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        specNorm A * ‖WithLp.toLp 2 v.p‖ ∧
      |v.p ⬝ᵥ sv - μ| ≤ cgImplementationRoundoffBound N (u tag) *
        ‖WithLp.toLp 2 v.p‖ * ‖WithLp.toLp 2 sv‖ ∧
      νnext = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θnext) ∧
      |θnext| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 ≤ νnext ∧
      (νnext = 0 ↔ next.r = 0) ∧ γ = ν / μ * (1 + eγ) ∧
      |eγ| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 < γ ∧
      δ = νnext / ν * (1 + eδ) ∧ |eδ| ≤ cgImplementationRoundoffBound N (u tag) ∧
      ‖WithLp.toLp 2 (v.x + γ • v.p - next.x)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.x‖ + |γ| * ‖WithLp.toLp 2 v.p‖) ∧
      ‖WithLp.toLp 2 (v.r - γ • sv - next.r)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 v.r‖ + |γ| * ‖WithLp.toLp 2 sv‖) ∧
      ‖WithLp.toLp 2 (next.r + δ • v.p - next.p)‖ ≤ cgImplementationRoundoffBound N (u tag) *
        (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 v.p‖) ∧
      (∃ w, out.store.read tag 7 3 = some w ∧ dec tag w = γ) ∧
      (∃ w, out.store.read tag 7 4 = some w ∧ dec tag w = δ) := by
  let active : St P K C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  obtain ⟨prestate, sv, μ, hprefix, hcpre, hs, hμ, hμpos, hes, heμ⟩ :=
    exec_rounded_curvature_prefix_pos I tag hsem hz active N A b v ν 0 flag h
      hN hsmall hA ha hspec hprec hp
  let guarded : St P K C := { prestate with cnt := prestate.cnt + I.charge (.cmp tag) }
  obtain ⟨out, next, νnext, θnext, γ, eγ, δ, eδ, hbody, hctx, hνeq, hθ, hnonneg, hzero,
      hγeq, heγ, hγpos, hδeq, heδ, hex, her, hep, hγ, hδ⟩ :=
    exec_rounded_positive_body I tag hsem hz guarded N A b v ν 0 flag μ sv
      hcpre hμ hs hνpos hμpos hN hsmall
  have hstatus := cmp_status_zero I tag hsem st N A b v ν flag h
  have hcurvature := cmp_curvature_positive I tag hsem prestate N A b v ν 0 flag μ hcpre hμ hμpos
  have hcompose : ExecutionComposable I (do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      (executionComposable_single I (fun _ => rfl))
  refine ⟨prestate, out, next, sv, μ, νnext, θnext, γ, eγ, δ, eδ, hprefix, ?_, hctx,
    hs, hμ, hμpos, hes, heμ, hνeq, hθ, hnonneg, hzero, hγeq, heγ, hγpos,
    hδeq, heδ, hex, her, hep, hγ, hδ⟩
  change exec I (.seq (.ite tag .eq ⟨4, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
  rw [exec_seq_skip, exec_ite, hstatus, Option.bind_some]
  change exec I ((do
    gemv tag (.const N) (.const N) 5 0 3 0 6 0
    dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)) >>= fun _ => _).run active = _
  rw [hcompose, hprefix, Option.bind_some]
  change exec I (.seq (.ite tag .lt ⟨7, 6⟩ ⟨7, 2⟩ _ _) .skip) prestate = _
  rw [exec_seq_skip, exec_ite, hcurvature, Option.bind_some]
  exact hbody

end NLAlib.CGImplementation
