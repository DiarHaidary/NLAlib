/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode.Split

/-!
# The set-up of the spectral bisection node step

The set-up of the node step of `NLAlib.eighProg`, up to the index binder of the split index: the
stored shift $\sigma$ and $-\sigma$, the sign step, the projectors and the value $\mathrm{fl}(t +
\mathrm{fl}(1/2))$ that the binder converts; only scratch buffers are written. Also the run of
`when` blocks and of index binders, as the node step uses them.

## Main results

* `NLAlib.node_setup_holds`: the values of the set-up.
* `NLAlib.loop_zero_node`, `NLAlib.loop_one_node`, `NLAlib.when_bind_node`, `NLAlib.when_run_node`,
  `NLAlib.bindIdx_inv_node`: the runs of the control blocks.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

omit [Inhabited K] in
private theorem node_inv_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.copy p dst src)) t) s = some s₂) :
    ∃ a s', s.store.read p src.buf src.idx.eval = some a ∧
      s.store.write p dst.buf dst.idx.eval a = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.copy p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, s', ha, hw, h⟩

omit [Inhabited K] in
/-- A trace keeps the shape of the store and the tape positions. -/
theorem shape_pos_of_exec_ztraceRe_node (p : P) (n : ℕ) {X : ℕ} {xo : IExp ℕ}
    {dst : Cell ℕ ℕ} {st st' : St P K C}
    (h : exec I (ztraceRe (ι := ι) p (.const n) X xo dst).run st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hins : ∀ {i : Instr P ℕ ℕ} {s s' : St P K C}, (∀ q d x, i ≠ .draw q d x) →
      exec I (.instr i) s = some s' → s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
    intro i s s' hi hs
    rw [exec_instr] at hs
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨Instr.shape_of_run_eq_some hr, ?_⟩
    cases i with
    | draw q d x => exact absurd rfl (hi q d x)
    | _ => simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr; aesop
  change exec I (.seq (.named _ _ (.seq (.instr _) (.seq (.loop _ _) .skip))) .skip) st =
    some st' at h
  rw [exec_seq_skip, exec_named, exec_seq] at h
  obtain ⟨s₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq_skip] at h
  obtain ⟨hsh₁, hps₁⟩ := hins (by intro _ _ _ h; cases h) h₁
  refine forall_of_exec_loop_eq_some I
    (fun _ s => s.store.shape = st.store.shape ∧ s.pos = st.pos) ⟨hsh₁, hps₁⟩ ?_ h
  rintro i - s₃ s₄ ⟨hsh, hps⟩ hex
  change exec I (.seq (.instr (.bin _ _ _ _ _)) .skip) s₃ = some s₄ at hex
  rw [exec_seq_skip] at hex
  obtain ⟨hsh₄, hps₄⟩ := hins (by intro _ _ _ h; cases h) hex
  exact ⟨hsh₄.trans hsh, hps₄.trans hps⟩

omit [Inhabited K] in
/-- A kernel block, then the rest. -/
private theorem node_bind {b : Builder P ι ℕ ℕ Unit} {X : Stmt P ι ℕ ℕ}
    (hb : ∀ k, ContT.run b k = .seq X (k ())) {f : Unit → Builder P ι ℕ ℕ Unit}
    {st st' : St P K C} (h : exec I (b >>= f).run st = some st') :
    ∃ σ, exec I b.run st = some σ ∧ exec I (f ()).run σ = some st' := by
  rw [exec_run_bind I hb] at h
  exact Option.bind_eq_some_iff.mp h

-- The set-up unfolds the instructions of the node step.
set_option maxHeartbeats 4000000 in
/-- The set-up of a node step, up to the index binder: the stored $\sigma$, $-\sigma$, the
projectors and $\mathrm{fl}(t + \mathrm{fl}(1/2))$; only scratch buffers (at handles from `s₀`)
are written. -/
theorem node_setup_holds {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n ℓ₀ F d lo k : ℕ) (hk : lo + k ≤ n) (H : EighArenas)
    {par Su c : ℕ} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R β : K}
    (s₀ : ℕ) (hlt : ∀ b ∈ H.handles ++ [par, Su, c], b < s₀)
    (t sp W B T Pp Pm : ℕ) (hge : ∀ X ∈ [t, sp, W, B, T, Pp, Pm], s₀ ≤ X)
    (hnd : [t, sp, W, B, T, Pp, Pm].Nodup)
    (hB : st.store.shape[B]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R)
    (hpar : st.store.read p par 2 = some β)
    (hSu : st.store.read p Su lo = some (I.tape .uniform (n * d + lo)))
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one))
    (rest : Builder P ι ℕ ℕ Unit)
    (h : exec I (do
      ins (.bin p .div ⟨t, 0⟩ ⟨H.Lv, 2 * .const d⟩ ⟨c, 1⟩)
      ins (.un p .neg ⟨t, 1⟩ ⟨t, 0⟩)
      ins (.litIdx p ⟨t, 2⟩ (.const ℓ₀ + .const d))
      ins (.bin p .div ⟨t, 3⟩ ⟨H.Lv, 2 * .const d⟩ ⟨t, 2⟩)
      ins (.bin p .mul ⟨t, 4⟩ ⟨t, 3⟩ ⟨Su, .const lo⟩)
      zhermShift p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo)) ⟨t, 4⟩ W 0
      ins (.copy p ⟨sp, 0⟩ ⟨par, 2⟩)
      ins (.bin p .mul ⟨sp, 1⟩ ⟨c, 1⟩ ⟨H.Lv, 2 * .const d⟩)
      eighSignBlock p mm (.const k) (.const F) W 0 sp 0 B 0
      zhermShift p (.const k) B 0 ⟨c, 3⟩ T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pp 0
      zhermShift p (.const k) B 0 ⟨c, 0⟩ T 0
      zneg p (.const k) (.const k) T 0 T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pm 0
      ztraceRe p (.const k) Pp 0 ⟨t, 5⟩
      ins (.bin p .add ⟨t, 6⟩ ⟨t, 5⟩ ⟨c, 2⟩)
      rest : Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let half := M.div R (M.ofNat 2)
    let B' := newtonSchulzSign M β (M.mul (M.ofNat 2) R) F
      (M.hermShift A (M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1))
    let Pp' := M.hermScale (M.hermShift B' (M.neg M.one)) (M.ofNat 2)
    let Pm' := M.hermScale (M.negMat (M.hermShift B' M.one)) (M.ofNat 2)
    ∃ σ : St P K C, exec I rest.run σ = some st' ∧
      (∀ q b i, b < s₀ → σ.store.read q b i = st.store.read q b i) ∧
      σ.store.shape = st.store.shape ∧ σ.pos = st.pos ∧
      σ.store.read p t 0 = some half ∧ σ.store.read p t 1 = some (M.neg half) ∧
      σ.store.read p t 6 = some (M.add (M.traceRe Pp') (M.div M.one (M.ofNat 2))) ∧
      pairLayout.Holds σ.store p Pp 0 Pp' ∧ pairLayout.Holds σ.store p Pm 0 Pm' ∧
      st.store.read p c 1 = some (M.ofNat 2) := by
  intro M half B' Pp' Pm'
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt hge
  obtain ⟨lMa, lUa, lQa, lEa, lSz, lKd, lKp, lLv, lpar, lSu, lc⟩ := hlt
  obtain ⟨gt, gsp, gW, gB, gT, gPp, gPm⟩ := hge
  have dtsp : t = sp → False := fun h => by simp [h] at hnd
  have dtW : t = W → False := fun h => by simp [h] at hnd
  have dtB : t = B → False := fun h => by simp [h] at hnd
  have dtT : t = T → False := fun h => by simp [h] at hnd
  have dtPp : t = Pp → False := fun h => by simp [h] at hnd
  have dtPm : t = Pm → False := fun h => by simp [h] at hnd
  have dspW : sp = W → False := fun h => by simp [h] at hnd
  have dspB : sp = B → False := fun h => by simp [h] at hnd
  have dWB : W = B → False := fun h => by simp [h] at hnd
  have dBT : B = T → False := fun h => by simp [h] at hnd
  have dBPp : B = Pp → False := fun h => by simp [h] at hnd
  have dBPm : B = Pm → False := fun h => by simp [h] at hnd
  have dTPp : T = Pp → False := fun h => by simp [h] at hnd
  have dTPm : T = Pm → False := fun h => by simp [h] at hnd
  have dPpPm : Pp = Pm → False := fun h => by simp [h] at hnd
  have bdl : ∀ {b X i off len : ℕ}, b < s₀ → s₀ ≤ X →
      blockDisjoint (b, i, 1) (X, off, len) = true := fun h1 h2 => by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact Or.inl (Or.inl (by omega))
  have bdn : ∀ {b X i i' off len : ℕ}, (b = X → False) →
      blockDisjoint (b, i, i') (X, off, len) = true := fun h => by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact Or.inl (Or.inl h)
  obtain ⟨z0, o, -, hl1, -, -⟩ := id hflag
  obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
  have hMone : M.one = o := by
    change (I.sem.lit p 1).getD default = o; rw [hl1, Option.getD_some]
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by
    simp [eighBlockOff]
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  -- 1. σ = R / fl(2)
  rw [hr] at h
  obtain ⟨aR, z2, v0, s1, haR, hz2, hv0, hw1, h⟩ := eighSignH_inv_bin h
  have eaR : aR = R := by
    change st.store.read p H.Lv (2 * d) = some aR at haR
    rw [hR] at haR; exact (Option.some_inj.mp haR).symm
  subst aR
  change st.store.read p c 1 = some z2 at hz2
  have hl2 : I.sem.lit p ((2 : ℕ) : ℚ) = some z2 := hc1.symm.trans hz2
  have hM2 : M.ofNat 2 = z2 := by
    change (I.sem.lit p ((2 : ℕ) : ℚ)).getD default = z2; rw [hl2, Option.getD_some]
  have hhalf : half = v0 := by
    change (I.sem.bin p .div R (M.ofNat 2)).getD default = v0; rw [hM2, hv0, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ1 e1s e1p h; simp only at e1s e1p; subst e1s
  have f1 : ∀ q b i, (b ≠ t ∨ i ≠ 0) → σ1.store.read q b i = st.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw1 hb
  -- 2. −σ
  rw [hr] at h
  obtain ⟨a1, v1, s2, ha1, hv1, hw2, h⟩ := eighSignH_inv_un h
  rw [Store.read_of_write_eq_some hw1, Option.some_inj] at ha1
  subst a1
  have hnhalf : M.neg half = v1 := by
    rw [hhalf]; change (I.sem.un p .neg _).getD default = v1; rw [hv1, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ2 e2s e2p h; simp only at e2s e2p; subst e2s
  have f2 : ∀ q b i, (b ≠ t ∨ i ≠ 1) → σ2.store.read q b i = σ1.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw2 hb
  -- 3. ℓ
  rw [hr] at h
  obtain ⟨v2, s3, hv2, hw3, h⟩ := eighSignH_inv_litIdx h
  have hMl : M.ofNat (ℓ₀ + d) = v2 := by
    change (I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD default = v2
    change I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ) = some v2 at hv2
    rw [hv2, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ3 e3s e3p h; simp only at e3s e3p; subst e3s
  have f3 : ∀ q b i, (b ≠ t ∨ i ≠ 2) → σ3.store.read q b i = σ2.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw3 hb
  -- 4. R / ℓ
  rw [hr] at h
  obtain ⟨aR', a2, v3, s4, haR', ha2, hv3, hw4, h⟩ := eighSignH_inv_bin h
  have eaR' : aR' = R := by
    change σ3.store.read p H.Lv (2 * d) = some aR' at haR'
    rw [f3 _ _ _ (Or.inl (by omega)), f2 _ _ _ (Or.inl (by omega)),
      f1 _ _ _ (Or.inl (by omega)), hR] at haR'
    exact (Option.some_inj.mp haR').symm
  subst aR'
  rw [Store.read_of_write_eq_some hw3, Option.some_inj] at ha2
  subst a2
  have hdiv3 : M.div R (M.ofNat (ℓ₀ + d)) = v3 := by
    rw [hMl]; change (I.sem.bin p .div R v2).getD default = v3; rw [hv3, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ4 e4s e4p h; simp only at e4s e4p; subst e4s
  have f4 : ∀ q b i, (b ≠ t ∨ i ≠ 3) → σ4.store.read q b i = σ3.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw4 hb
  -- 5. the shift c
  rw [hr] at h
  obtain ⟨a3, au, v4, s5, ha3, hau, hv4, hw5, h⟩ := eighSignH_inv_bin h
  rw [Store.read_of_write_eq_some hw4, Option.some_inj] at ha3
  subst a3
  have eau : au = I.tape .uniform (n * d + lo) := by
    change σ4.store.read p Su lo = some au at hau
    rw [f4 _ _ _ (Or.inl (by omega)), f3 _ _ _ (Or.inl (by omega)),
      f2 _ _ _ (Or.inl (by omega)), f1 _ _ _ (Or.inl (by omega)), hSu] at hau
    exact (Option.some_inj.mp hau).symm
  subst au
  have hunif : M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1 = v4 := by
    rw [hdiv3]
    change (I.sem.bin p .mul v3 (I.tape .uniform (n * d + lo))).getD default = v4
    rw [hv4, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ5 e5s e5p h; simp only at e5s e5p; subst e5s
  have f5 : ∀ q b i, (b ≠ t ∨ i ≠ 4) → σ5.store.read q b i = σ4.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw5 hb
  have lo5 : ∀ q b i, b < s₀ → σ5.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f5 _ _ _ (Or.inl (by omega)), f4 _ _ _ (Or.inl (by omega)),
      f3 _ _ _ (Or.inl (by omega)), f2 _ _ _ (Or.inl (by omega)), f1 _ _ _ (Or.inl (by omega))]
  -- 6. W = A − cI
  obtain ⟨σ6, h6, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hW6, hf6, hsh6, hp6⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ5) (st' := σ6)
    (by rw [hbo]; exact fun i j t => (lo5 _ _ _ (by omega)).trans (hA i j t))
    (Store.read_of_write_eq_some hw5) (bdn (fun h => by omega)) (bdn dtW) h6
  have f6 : ∀ q b i, (b = W → False) → σ6.store.read q b i = σ5.store.read q b i :=
    fun q b i hb => hf6 q b i (bdn hb)
  -- 7. β
  rw [hr] at h
  obtain ⟨aβ, s7, haβ, hw7, h⟩ := node_inv_copy h
  have eaβ : aβ = β := by
    change σ6.store.read p par 2 = some aβ at haβ
    rw [f6 _ _ _ (fun h => by omega), lo5 _ _ _ lpar, hpar] at haβ
    exact (Option.some_inj.mp haβ).symm
  subst aβ
  refine name_state_node h ?_; clear h; intro σ7 e7s e7p h; simp only at e7s e7p; subst e7s
  have f7 : ∀ q b i, (b ≠ sp ∨ i ≠ 0) → σ7.store.read q b i = σ6.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw7 hb
  -- 8. fl(2) R
  rw [hr] at h
  obtain ⟨a5, a6, vb, s8, ha5, ha6, hvb, hw8, h⟩ := eighSignH_inv_bin h
  have ea5 : a5 = z2 := by
    change σ7.store.read p c 1 = some a5 at ha5
    rw [f7 _ _ _ (Or.inl (by omega)), f6 _ _ _ (fun h => by omega), lo5 _ _ _ lc, hz2] at ha5
    exact (Option.some_inj.mp ha5).symm
  subst a5
  have ea6 : a6 = R := by
    change σ7.store.read p H.Lv (2 * d) = some a6 at ha6
    rw [f7 _ _ _ (Or.inl (by omega)), f6 _ _ _ (fun h => by omega), lo5 _ _ _ lLv, hR] at ha6
    exact (Option.some_inj.mp ha6).symm
  subst a6
  have hmul : M.mul (M.ofNat 2) R = vb := by
    rw [hM2]; change (I.sem.bin p .mul z2 R).getD default = vb; rw [hvb, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ8 e8s e8p h; simp only at e8s e8p; subst e8s
  have f8 : ∀ q b i, (b ≠ sp ∨ i ≠ 1) → σ8.store.read q b i = σ7.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw8 hb
  have hsh8 : σ8.store.shape = st.store.shape := by
    rw [Store.shape_of_write_eq_some hw8, Store.shape_of_write_eq_some hw7, hsh6,
      Store.shape_of_write_eq_some hw5, Store.shape_of_write_eq_some hw4,
      Store.shape_of_write_eq_some hw3, Store.shape_of_write_eq_some hw2,
      Store.shape_of_write_eq_some hw1]
  -- 9. the sign
  obtain ⟨σ9, h9, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hB9, hf9, hsh9, hp9⟩ := holds_of_exec_eighSignBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p hflag k F (A := W) (ao := 0) (par := sp) (po := 0) (X := B) (xo := 0)
    (st := σ8) (st' := σ9)
    (fun i j t => (f8 _ _ _ (Or.inl (fun h => dspW h.symm))).trans
      ((f7 _ _ _ (Or.inl (fun h => dspW h.symm))).trans (hW6 i j t)))
    (show σ8.store.read p sp 0 = some β from
      (f8 _ _ _ (Or.inr (by omega))).trans (Store.read_of_write_eq_some hw7))
    (show σ8.store.read p sp 1 = some vb from Store.read_of_write_eq_some hw8)
    (bdn (fun h => dWB h.symm)) (bdn (fun h => dspB h.symm))
    ⟨2 * (n * n), by rw [hsh8]; exact hB, by simp only [IExp.eval_zero]; omega⟩ h9
  have f9 : ∀ q b i, (b = B → False) → σ9.store.read q b i = σ8.store.read q b i :=
    fun q b i hb => hf9 q b i (bdn hb)
  have lo9 : ∀ q b i, b < s₀ → σ9.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f9 _ _ _ (fun h => by omega), f8 _ _ _ (Or.inl (by omega)),
      f7 _ _ _ (Or.inl (by omega)), f6 _ _ _ (fun h => by omega), lo5 _ _ _ hb]
  have hB' : B' = newtonSchulzSign M β vb F (M.hermShift A v4) := by
    show newtonSchulzSign M β (M.mul (M.ofNat 2) R) F
      (M.hermShift A (M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1)) = _
    rw [hmul, hunif]
  -- 10. T = B + I
  obtain ⟨σ10, h10, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hT10, hf10, hsh10, hp10⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ9) (st' := σ10) hB9 (show σ9.store.read p c 3 = _ from (lo9 _ _ _ lc).trans hc3)
    (bdn (fun h => dBT h.symm)) (bdn (fun h => by simp only at h; omega)) h10
  have f10 : ∀ q b i, (b = T → False) → σ10.store.read q b i = σ9.store.read q b i :=
    fun q b i hb => hf10 q b i (bdn hb)
  -- 11. P₊
  obtain ⟨σ11, h11, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hPp11, hf11, hsh11, hp11⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ10) (st' := σ11) hT10
    (show σ10.store.read p c 1 = some z2 from
      (f10 _ _ _ (fun h => by omega)).trans ((lo9 _ _ _ lc).trans hz2))
    (bdn (fun h => dTPp h.symm)) (bdn (fun h => by simp only at h; omega)) h11
  have f11 : ∀ q b i, (b = Pp → False) → σ11.store.read q b i = σ10.store.read q b i :=
    fun q b i hb => hf11 q b i (bdn hb)
  -- 12. T = B − I
  obtain ⟨σ12, h12, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hT12, hf12, hsh12, hp12⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ11) (st' := σ12)
    (fun i j t => (f11 _ _ _ dBPp).trans ((f10 _ _ _ dBT).trans (hB9 i j t)))
    (show σ11.store.read p c 0 = some o from (f11 _ _ _ (fun h => by omega)).trans
      ((f10 _ _ _ (fun h => by omega)).trans ((lo9 _ _ _ lc).trans (hc0.trans hl1))))
    (bdn (fun h => dBT h.symm)) (bdn (fun h => by simp only at h; omega)) h12
  have f12 : ∀ q b i, (b = T → False) → σ12.store.read q b i = σ11.store.read q b i :=
    fun q b i hb => hf12 q b i (bdn hb)
  -- 13. T = −T
  obtain ⟨σ13, h13, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hT13, hf13, hsh13, hp13⟩ := holds_of_exec_zneg
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k k (st := σ12) (st' := σ13) hT12 (Or.inr ⟨rfl, rfl⟩) h13
  have f13 : ∀ q b i, (b = T → False) → σ13.store.read q b i = σ12.store.read q b i :=
    fun q b i hb => hf13 q b i (bdn hb)
  -- 14. P₋
  obtain ⟨σ14, h14, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hPm14, hf14, hsh14, hp14⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ13) (st' := σ14) hT13
    (show σ13.store.read p c 1 = some z2 from (f13 _ _ _ (fun h => by omega)).trans
      ((f12 _ _ _ (fun h => by omega)).trans ((f11 _ _ _ (fun h => by omega)).trans
        ((f10 _ _ _ (fun h => by omega)).trans ((lo9 _ _ _ lc).trans hz2)))))
    (bdn (fun h => dTPm h.symm)) (bdn (fun h => by simp only at h; omega)) h14
  have f14 : ∀ q b i, (b = Pm → False) → σ14.store.read q b i = σ13.store.read q b i :=
    fun q b i hb => hf14 q b i (bdn hb)
  have hPp14 : pairLayout.Holds σ14.store p Pp 0
      ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermScale
        ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
          (I.sem.tapeUnif p (I.tape .uniform))
          (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
          (newtonSchulzSign M β vb F (M.hermShift A v4)) (M.neg M.one)) z2) :=
    fun i j t => (f14 _ _ _ dPpPm).trans ((f13 _ _ _ (fun h => dTPp h.symm)).trans
      ((f12 _ _ _ (fun h => dTPp h.symm)).trans (hPp11 i j t)))
  -- 15. the trace
  obtain ⟨σ15, h15, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨htr15, hf15⟩ := read_of_exec_ztraceRe
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ14) (st' := σ15) hPp14 (bdn dtPp) h15
  obtain ⟨hsh15, hp15⟩ := shape_pos_of_exec_ztraceRe_node p k h15
  have f15 : ∀ q b i, (b ≠ t ∨ i ≠ 5) → σ15.store.read q b i = σ14.store.read q b i := by
    intro q b i hb
    refine hf15 q b i ?_
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    change (b ≠ t ∨ i + 1 ≤ 5) ∨ 5 + 1 ≤ i
    omega
  -- 16. t + 1/2
  rw [hr] at h
  obtain ⟨a7, a8, v6, s16, ha7, ha8, hv6, hw16, h⟩ := eighSignH_inv_bin h
  have e : Pp' = M.hermScale (M.hermShift (newtonSchulzSign M β vb F (M.hermShift A v4))
      (M.neg M.one)) z2 := by
    show M.hermScale (M.hermShift B' (M.neg M.one)) (M.ofNat 2) = _
    rw [hB', hM2]
  have e' : Pm' = M.hermScale (M.negMat (M.hermShift (newtonSchulzSign M β vb F
      (M.hermShift A v4)) M.one)) z2 := by
    show M.hermScale (M.negMat (M.hermShift B' M.one)) (M.ofNat 2) = _
    rw [hB', hM2]
  have ea7 : a7 = (M.traceRe Pp') := by
    rw [e]
    exact (Option.some_inj.mp (ha7.symm.trans htr15))
  subst a7
  have ea8 : a8 = M.div M.one (M.ofNat 2) := by
    change σ15.store.read p c 2 = some a8 at ha8
    rw [f15 _ _ _ (Or.inl (by omega)), f14 _ _ _ (fun h => by omega),
      f13 _ _ _ (fun h => by omega), f12 _ _ _ (fun h => by omega),
      f11 _ _ _ (fun h => by omega), f10 _ _ _ (fun h => by omega), lo9 _ _ _ lc, hc2] at ha8
    exact (Option.some_inj.mp ha8).symm
  subst a8
  have f16 : ∀ q b i, (b ≠ t ∨ i ≠ 6) → s16.read q b i = σ15.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw16 hb
  refine ⟨_, h, fun q b i hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hM2]; exact hz2⟩
  · change s16.read q b i = _
    rw [f16 _ _ _ (Or.inl (by omega)), f15 _ _ _ (Or.inl (by omega)),
      f14 _ _ _ (fun h => by omega), f13 _ _ _ (fun h => by omega),
      f12 _ _ _ (fun h => by omega), f11 _ _ _ (fun h => by omega),
      f10 _ _ _ (fun h => by omega), lo9 _ _ _ hb]
  · change s16.shape = _
    rw [Store.shape_of_write_eq_some hw16, hsh15, hsh14, hsh13, hsh12, hsh11, hsh10, hsh9, hsh8]
  · change σ15.pos = st.pos
    rw [hp15, hp14, hp13, hp12, hp11, hp10, hp9, e8p, e7p, hp6, e5p, e4p, e3p, e2p, e1p]
  · change s16.read p t 0 = _
    rw [f16 _ _ _ (Or.inr (by omega)), f15 _ _ _ (Or.inr (by omega)), f14 _ _ _ dtPm,
      f13 _ _ _ dtT, f12 _ _ _ dtT, f11 _ _ _ dtPp, f10 _ _ _ dtT, f9 _ _ _ dtB,
      f8 _ _ _ (Or.inl dtsp), f7 _ _ _ (Or.inl dtsp), f6 _ _ _ dtW,
      f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)), f3 _ _ _ (Or.inr (by omega)),
      f2 _ _ _ (Or.inr (by omega)), hhalf]
    exact Store.read_of_write_eq_some hw1
  · change s16.read p t 1 = _
    rw [f16 _ _ _ (Or.inr (by omega)), f15 _ _ _ (Or.inr (by omega)), f14 _ _ _ dtPm,
      f13 _ _ _ dtT, f12 _ _ _ dtT, f11 _ _ _ dtPp, f10 _ _ _ dtT, f9 _ _ _ dtB,
      f8 _ _ _ (Or.inl dtsp), f7 _ _ _ (Or.inl dtsp), f6 _ _ _ dtW,
      f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)), f3 _ _ _ (Or.inr (by omega)),
      hnhalf]
    exact Store.read_of_write_eq_some hw2
  · show s16.read p t 6 = some ((I.sem.bin p .add _ _).getD default)
    rw [hv6, Option.getD_some]
    exact Store.read_of_write_eq_some hw16
  · rw [e]
    exact fun i j t' => (f16 _ _ _ (Or.inl (fun h => dtPp h.symm))).trans
      ((f15 _ _ _ (Or.inl (fun h => dtPp h.symm))).trans (hPp14 i j t'))
  · rw [e', hMone]
    exact fun i j t' => (f16 _ _ _ (Or.inl (fun h => dtPm h.symm))).trans
      ((f15 _ _ _ (Or.inl (fun h => dtPm h.symm))).trans (hPm14 i j t'))

omit [Inhabited K] in
/-- A loop of no iterations. -/
theorem loop_zero_node {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 0) (h : exec I (.seq (.loop e b) .skip) s = some s') : s' = s := by
  rw [exec_seq_skip, exec_loop, he] at h
  simp only [List.range_zero, List.foldlM_nil] at h
  exact (Option.some_inj.mp h).symm

omit [Inhabited K] in
/-- A loop of one iteration. -/
theorem loop_one_node {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 1) (h : exec I (.seq (.loop e b) .skip) s = some s') :
    exec I (b 0) s = some s' := by
  rw [exec_seq_skip, exec_loop, he] at h
  simpa [List.range_one] using h

omit [Inhabited K] in
/-- A guarded block, then the rest. -/
theorem when_bind_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {st st' : St P K C}
    (h : exec I (eighWhen e b >>= f).run st = some st') :
    ∃ σ, exec I (.seq (.loop (1 - (1 - e)) fun _ => b.run) .skip) st = some σ ∧
      exec I (f ()).run σ = some st' := node_bind (fun _ => rfl) h

omit [Inhabited K] in
/-- A guarded block. -/
theorem when_run_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit} {st st' : St P K C}
    (h : exec I (eighWhen e b).run st = some st') :
    exec I (.seq (.loop (1 - (1 - e)) fun _ => b.run) .skip) st = some st' := h

omit [Inhabited K] in
/-- The run of a scoped index binder, inverted. -/
theorem bindIdx_inv_node {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.seq (.bindIdx p x bound body) .skip) st = some st') :
    ∃ v w, st.store.read p x.buf x.idx.eval = some w ∧ I.sem.toNat p w = some v ∧
      v ≤ bound.eval ∧
      exec I (body v) { st with cnt := st.cnt + I.charge (.toNat p) } = some st' := by
  rw [exec_seq_skip, exec_bindIdx] at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  unfold toNatStep at hr
  obtain ⟨w, hw, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hr
  split_ifs at h with hle
  exact ⟨v, w, hw, hv, hle, h⟩

end NLAlib
