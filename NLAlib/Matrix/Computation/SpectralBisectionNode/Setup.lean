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
\mathrm{fl}(1/2))$ that the binder converts; only scratch buffers are written.

## Main results

* `NLAlib.node_setup_holds`: the values of the set-up.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

omit [Inhabited K] in
/-- A successful copy, then the rest, inverted: the value copied, the write and the run of the
rest. -/
private theorem exists_of_exec_seq_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
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

omit [Inhabited K] in
/-- A successful index literal, then the rest, inverted: the literal's value, the write and the
run of the rest. -/
private theorem exists_of_exec_seq_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ}
    {t : Stmt P ι ℕ ℕ} {s s₂ : St P K C}
    (h : exec I (.seq (.instr (.litIdx p dst e)) t) s = some s₂) :
    ∃ v s', I.sem.lit p (e.eval : ℚ) = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
/-- A successful binary operation, then the rest, inverted: the operands, the value, the write
and the run of the rest. -/
private theorem exists_of_exec_seq_bin {p : P} {op : BinOp} {dst x y : Cell ℕ ℕ}
    {t : Stmt P ι ℕ ℕ} {s s₂ : St P K C}
    (h : exec I (.seq (.instr (.bin p op dst x y)) t) s = some s₂) :
    ∃ a c v s', s.store.read p x.buf x.idx.eval = some a ∧
      s.store.read p y.buf y.idx.eval = some c ∧ I.sem.bin p op a c = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p op) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, c, hc, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, c, v, s', ha, hc, hv, hw, h⟩

omit [Inhabited K] in
/-- A successful unary operation, then the rest, inverted: the operand, the value, the write and
the run of the rest. -/
private theorem exists_of_exec_seq_un {p : P} {u : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.un p u dst x)) t) s = some s₂) :
    ∃ a v s', s.store.read p x.buf x.idx.eval = some a ∧ I.sem.un p u a = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.un p u) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, v, s', ha, hv, hw, h⟩

/-- The scalars of a node step's set-up: from a state whose cell $2d$ of `Lv` holds $R$, whose
cell `lo` of `Su` holds the node's uniform word and whose cell $1$ of `c` holds the stored $2$,
five instructions write $\sigma = R/\mathrm{fl}(2)$, $-\sigma$ and the shift
$\mathrm{unif}(R/\mathrm{fl}(\ell_0 + d), u)$ in the cells $0$, $1$, $4$ of the scratch buffer
`t` (none of the others); only cells of `t` change. -/
private theorem node_setup_scalars (p : P) (n ℓ₀ d lo : ℕ) (H : EighArenas) {t Su c : ℕ}
    {st st' : St P K C} {R : K} (dtLv : t = H.Lv → False) (dtSu : t = Su → False)
    (hR : st.store.read p H.Lv (2 * d) = some R)
    (hSu : st.store.read p Su lo = some (I.tape .uniform (n * d + lo)))
    (hc1 : st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (rest : Builder P ι ℕ ℕ Unit)
    (h : exec I (do
      ins (.bin p .div ⟨t, 0⟩ ⟨H.Lv, 2 * .const d⟩ ⟨c, 1⟩)
      ins (.un p .neg ⟨t, 1⟩ ⟨t, 0⟩)
      ins (.litIdx p ⟨t, 2⟩ (.const ℓ₀ + .const d))
      ins (.bin p .div ⟨t, 3⟩ ⟨H.Lv, 2 * .const d⟩ ⟨t, 2⟩)
      ins (.bin p .mul ⟨t, 4⟩ ⟨t, 3⟩ ⟨Su, .const lo⟩)
      rest : Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    ∃ σ : St P K C, exec I rest.run σ = some st' ∧
      (∀ q b i, (b = t → False) → σ.store.read q b i = st.store.read q b i) ∧
      σ.store.shape = st.store.shape ∧ σ.pos = st.pos ∧
      σ.store.read p t 0 = some (M.div R (M.ofNat 2)) ∧
      σ.store.read p t 1 = some (M.neg (M.div R (M.ofNat 2))) ∧
      σ.store.read p t 4 =
        some (M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1) ∧
      st.store.read p c 1 = some (M.ofNat 2) := by
  intro M
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  -- σ = R / fl(2)
  rw [hr] at h
  obtain ⟨aR, z2, v0, s1, haR, hz2, hv0, hw1, h⟩ := exists_of_exec_seq_bin h
  change st.store.read p H.Lv (2 * d) = some aR at haR
  change st.store.read p c 1 = some z2 at hz2
  rw [hR, Option.some_inj] at haR
  subst haR
  have hM2 : M.ofNat 2 = z2 := by
    change (I.sem.lit p ((2 : ℕ) : ℚ)).getD default = z2; rw [← hc1, hz2, Option.getD_some]
  subst hM2
  have hhalf : M.div R (M.ofNat 2) = v0 := by
    change (I.sem.bin p .div R (M.ofNat 2)).getD default = v0; rw [hv0, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ1 e1s e1p h; simp only at e1s e1p; subst e1s
  have f1 : ∀ q b i, (b ≠ t ∨ i ≠ 0) → σ1.store.read q b i = st.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw1 hb
  -- −σ
  rw [hr] at h
  obtain ⟨a1, v1, s2, ha1, hv1, hw2, h⟩ := exists_of_exec_seq_un h
  rw [Store.read_of_write_eq_some hw1, Option.some_inj] at ha1
  subst a1
  have hnhalf : M.neg (M.div R (M.ofNat 2)) = v1 := by
    rw [hhalf]; change (I.sem.un p .neg _).getD default = v1; rw [hv1, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ2 e2s e2p h; simp only at e2s e2p; subst e2s
  have f2 : ∀ q b i, (b ≠ t ∨ i ≠ 1) → σ2.store.read q b i = σ1.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw2 hb
  -- ℓ
  rw [hr] at h
  obtain ⟨v2, s3, hv2, hw3, h⟩ := exists_of_exec_seq_litIdx h
  have hMl : M.ofNat (ℓ₀ + d) = v2 := by
    change (I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD default = v2
    change I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ) = some v2 at hv2
    rw [hv2, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ3 e3s e3p h; simp only at e3s e3p; subst e3s
  have f3 : ∀ q b i, (b ≠ t ∨ i ≠ 2) → σ3.store.read q b i = σ2.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw3 hb
  -- R / ℓ
  rw [hr] at h
  obtain ⟨aR', a2, v3, s4, haR', ha2, hv3, hw4, h⟩ := exists_of_exec_seq_bin h
  change σ3.store.read p H.Lv (2 * d) = some aR' at haR'
  rw [f3 _ _ _ (Or.inl fun h => dtLv h.symm), f2 _ _ _ (Or.inl fun h => dtLv h.symm),
    f1 _ _ _ (Or.inl fun h => dtLv h.symm), hR, Option.some_inj] at haR'
  subst aR'
  rw [Store.read_of_write_eq_some hw3, Option.some_inj] at ha2
  subst a2
  have hdiv3 : M.div R (M.ofNat (ℓ₀ + d)) = v3 := by
    rw [hMl]; change (I.sem.bin p .div R v2).getD default = v3; rw [hv3, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ4 e4s e4p h; simp only at e4s e4p; subst e4s
  have f4 : ∀ q b i, (b ≠ t ∨ i ≠ 3) → σ4.store.read q b i = σ3.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw4 hb
  -- the shift
  rw [hr] at h
  obtain ⟨a3, au, v4, s5, ha3, hau, hv4, hw5, h⟩ := exists_of_exec_seq_bin h
  rw [Store.read_of_write_eq_some hw4, Option.some_inj] at ha3
  subst a3
  change σ4.store.read p Su lo = some au at hau
  rw [f4 _ _ _ (Or.inl fun h => dtSu h.symm), f3 _ _ _ (Or.inl fun h => dtSu h.symm),
    f2 _ _ _ (Or.inl fun h => dtSu h.symm), f1 _ _ _ (Or.inl fun h => dtSu h.symm), hSu,
    Option.some_inj] at hau
  subst au
  have hunif : M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1 = v4 := by
    rw [hdiv3]
    change (I.sem.bin p .mul v3 (I.tape .uniform (n * d + lo))).getD default = v4
    rw [hv4, Option.getD_some]
  have f5 : ∀ q b i, (b ≠ t ∨ i ≠ 4) → s5.read q b i = σ4.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw5 hb
  refine ⟨_, h, fun q b i hb => ?_, ?_, e4p.trans (e3p.trans (e2p.trans e1p)), ?_, ?_, ?_, hz2⟩
  · change s5.read q b i = _
    rw [f5 _ _ _ (Or.inl hb), f4 _ _ _ (Or.inl hb), f3 _ _ _ (Or.inl hb), f2 _ _ _ (Or.inl hb),
      f1 _ _ _ (Or.inl hb)]
  · change s5.shape = _
    rw [Store.shape_of_write_eq_some hw5, Store.shape_of_write_eq_some hw4,
      Store.shape_of_write_eq_some hw3, Store.shape_of_write_eq_some hw2,
      Store.shape_of_write_eq_some hw1]
  · change s5.read p t 0 = _
    rw [f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)), f3 _ _ _ (Or.inr (by omega)),
      f2 _ _ _ (Or.inr (by omega)), hhalf]
    exact Store.read_of_write_eq_some hw1
  · change s5.read p t 1 = _
    rw [f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)), f3 _ _ _ (Or.inr (by omega)),
      hnhalf]
    exact Store.read_of_write_eq_some hw2
  · rw [hunif]; exact Store.read_of_write_eq_some hw5

/-- The sign of a node step's set-up: from a state whose node matrix $\mathbf{A}$ is held at its
block of `Ma`, whose cell $4$ of `t` holds the shift $c$, cell $2$ of `par` holds $\beta$, cell
$1$ of `c` the stored $2$ and cell $2d$ of `Lv` holds $R$, the block writes
$\mathbf{W} = \mathbf{A} - c\mathbf{I}$ in `W`, $\beta$ and $\mathrm{fl}(2) R$ in the cells $0$, $1$
of `sp` and the sign of $\mathbf{W}$ (step limit $F$) in `B` (three scratch buffers, distinct and
none of the others); only cells of `W`, `sp`, `B` change. -/
private theorem node_setup_sign {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n F d lo k : ℕ) (hk : lo + k ≤ n) (H : EighArenas)
    {par c t sp W B : ℕ} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R β cv : K}
    (dMaW : H.Ma = W → False) (dtW : t = W → False) (dparW : par = W → False)
    (dcW : c = W → False) (dLvW : H.Lv = W → False) (dcsp : c = sp → False)
    (dLvsp : H.Lv = sp → False) (dspW : sp = W → False)
    (dspB : sp = B → False) (dWB : W = B → False)
    (hB : st.store.shape[B]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hcv : st.store.read p t 4 = some cv) (hpar : st.store.read p par 2 = some β)
    (hc1 : st.store.read p c 1 = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hR : st.store.read p H.Lv (2 * d) = some R) (rest : Builder P ι ℕ ℕ Unit)
    (h : exec I (do
      zhermShift p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo)) ⟨t, 4⟩ W 0
      ins (.copy p ⟨sp, 0⟩ ⟨par, 2⟩)
      ins (.bin p .mul ⟨sp, 1⟩ ⟨c, 1⟩ ⟨H.Lv, 2 * .const d⟩)
      eighSignBlock p mm (.const k) (.const F) W 0 sp 0 B 0
      rest : Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    ∃ σ : St P K C, exec I rest.run σ = some st' ∧
      (∀ q b i, (b = W → False) → (b = sp → False) → (b = B → False) →
        σ.store.read q b i = st.store.read q b i) ∧
      σ.store.shape = st.store.shape ∧ σ.pos = st.pos ∧
      pairLayout.Holds σ.store p B 0
        (newtonSchulzSign M β (M.mul (M.ofNat 2) R) F (M.hermShift A cv)) := by
  intro M
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have bdn : ∀ {b X i i' off len : ℕ}, (b = X → False) →
      blockDisjoint (b, i, i') (X, off, len) = true := fun h => by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact Or.inl (Or.inl h)
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by simp [eighBlockOff]
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  -- W = A − cI
  obtain ⟨σ6, h6, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hW6, hf6, hsh6, hp6⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := st) (st' := σ6) (by rw [hbo]; exact hA) hcv (bdn fun h => dMaW h.symm) (bdn dtW) h6
  have f6 : ∀ q b i, (b = W → False) → σ6.store.read q b i = st.store.read q b i :=
    fun q b i hb => hf6 q b i (bdn hb)
  -- β
  rw [hr] at h
  obtain ⟨aβ, s7, haβ, hw7, h⟩ := exists_of_exec_seq_copy h
  change σ6.store.read p par 2 = some aβ at haβ
  rw [f6 _ _ _ dparW, hpar, Option.some_inj] at haβ
  subst aβ
  refine name_state_node h ?_; clear h; intro σ7 e7s e7p h; simp only at e7s e7p; subst e7s
  have f7 : ∀ q b i, (b ≠ sp ∨ i ≠ 0) → σ7.store.read q b i = σ6.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw7 hb
  -- fl(2) R
  rw [hr] at h
  obtain ⟨a5, a6, vb, s8, ha5, ha6, hvb, hw8, h⟩ := exists_of_exec_seq_bin h
  change σ7.store.read p c 1 = some a5 at ha5
  rw [f7 _ _ _ (Or.inl dcsp), f6 _ _ _ dcW, hc1, Option.some_inj] at ha5
  subst a5
  change σ7.store.read p H.Lv (2 * d) = some a6 at ha6
  rw [f7 _ _ _ (Or.inl dLvsp), f6 _ _ _ dLvW, hR, Option.some_inj] at ha6
  subst a6
  have hmul : M.mul (M.ofNat 2) R = vb := by
    change (I.sem.bin p .mul (M.ofNat 2) R).getD default = vb; rw [hvb, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ8 e8s e8p h; simp only at e8s e8p; subst e8s
  have f8 : ∀ q b i, (b ≠ sp ∨ i ≠ 1) → σ8.store.read q b i = σ7.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw8 hb
  have hsh8 : σ8.store.shape = st.store.shape := by
    rw [Store.shape_of_write_eq_some hw8, Store.shape_of_write_eq_some hw7, hsh6]
  -- the sign
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
  refine ⟨σ9, h, fun q b i hW hsp hbB => ?_, hsh9.trans hsh8,
    hp9.trans (e8p.trans (e7p.trans hp6)), by rw [hmul]; exact hB9⟩
  rw [hf9 q b i (bdn hbB), f8 _ _ _ (Or.inl hsp), f7 _ _ _ (Or.inl hsp), f6 _ _ _ hW]

/-- The projectors of a node step's set-up: from a state whose block at offset $0$ of `B` holds
the sign $\mathbf{B}$ and whose cells $0$, $1$, $3$ of `c` hold the stored $1$, $2$ and $-1$, the
block writes $\mathbf{P}_+ = (\mathbf{B} + \mathbf{I})/\mathrm{fl}(2)$ in `Pp` and
$\mathbf{P}_- = -(\mathbf{B} - \mathbf{I})/\mathrm{fl}(2)$ in `Pm`, through the scratch buffer `T`
(the four buffers distinct and `c` none of them); only cells of `T`, `Pp`, `Pm` change. -/
private theorem node_setup_projectors (p : P) (k : ℕ) {c B T Pp Pm : ℕ} {st st' : St P K C}
    {Bm : Matrix (Fin k) (Fin k) (K × K)} {o : K} (dBT : B = T → False) (dBPp : B = Pp → False)
    (dTPp : T = Pp → False) (dTPm : T = Pm → False) (dPpPm : Pp = Pm → False)
    (dcT : c = T → False) (dcPp : c = Pp → False) (dcPm : c = Pm → False)
    (hB : pairLayout.Holds st.store p B 0 Bm) (hc0 : st.store.read p c 0 = some o)
    (hc1 : st.store.read p c 1 = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hc3 : st.store.read p c 3 =
      some ((eighTapeMachine I p mmR qrR).neg (eighTapeMachine I p mmR qrR).one))
    (rest : Builder P ι ℕ ℕ Unit)
    (h : exec I (do
      zhermShift p (.const k) B 0 ⟨c, 3⟩ T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pp 0
      zhermShift p (.const k) B 0 ⟨c, 0⟩ T 0
      zneg p (.const k) (.const k) T 0 T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pm 0
      rest : Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    ∃ σ : St P K C, exec I rest.run σ = some st' ∧
      (∀ q b i, (b = T → False) → (b = Pp → False) → (b = Pm → False) →
        σ.store.read q b i = st.store.read q b i) ∧
      σ.store.shape = st.store.shape ∧ σ.pos = st.pos ∧
      pairLayout.Holds σ.store p Pp 0 (M.hermScale (M.hermShift Bm (M.neg M.one)) (M.ofNat 2)) ∧
      pairLayout.Holds σ.store p Pm 0 (M.hermScale (M.negMat (M.hermShift Bm o)) (M.ofNat 2)) := by
  intro M
  have bdn : ∀ {b X i i' off len : ℕ}, (b = X → False) →
      blockDisjoint (b, i, i') (X, off, len) = true := fun h => by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact Or.inl (Or.inl h)
  -- T = B + I
  obtain ⟨σ10, h10, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hT10, hf10, hsh10, hp10⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := st) (st' := σ10) hB hc3 (bdn (fun h => dBT h.symm)) (bdn dcT) h10
  have f10 : ∀ q b i, (b = T → False) → σ10.store.read q b i = st.store.read q b i :=
    fun q b i hb => hf10 q b i (bdn hb)
  -- P₊
  obtain ⟨σ11, h11, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hPp11, hf11, hsh11, hp11⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ10) (st' := σ11) hT10 ((f10 _ _ _ dcT).trans hc1)
    (bdn (fun h => dTPp h.symm)) (bdn dcPp) h11
  have f11 : ∀ q b i, (b = Pp → False) → σ11.store.read q b i = σ10.store.read q b i :=
    fun q b i hb => hf11 q b i (bdn hb)
  -- T = B − I
  have hB11 : pairLayout.Holds σ11.store p B (0 : IExp ℕ).eval Bm :=
    fun i j t => (f11 _ _ _ dBPp).trans ((f10 _ _ _ dBT).trans (hB i j t))
  obtain ⟨σ12, h12, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hT12, hf12, hsh12, hp12⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ11) (st' := σ12) hB11 ((f11 _ _ _ dcPp).trans ((f10 _ _ _ dcT).trans hc0))
    (bdn (fun h => dBT h.symm)) (bdn dcT) h12
  have f12 : ∀ q b i, (b = T → False) → σ12.store.read q b i = σ11.store.read q b i :=
    fun q b i hb => hf12 q b i (bdn hb)
  -- T = −T
  obtain ⟨σ13, h13, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hT13, hf13, hsh13, hp13⟩ := holds_of_exec_zneg
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k k (st := σ12) (st' := σ13) hT12 (Or.inr ⟨rfl, rfl⟩) h13
  have f13 : ∀ q b i, (b = T → False) → σ13.store.read q b i = σ12.store.read q b i :=
    fun q b i hb => hf13 q b i (bdn hb)
  -- P₋
  obtain ⟨σ14, h14, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hPm14, hf14, hsh14, hp14⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ13) (st' := σ14) hT13
    ((f13 _ _ _ dcT).trans ((f12 _ _ _ dcT).trans ((f11 _ _ _ dcPp).trans
      ((f10 _ _ _ dcT).trans hc1))))
    (bdn (fun h => dTPm h.symm)) (bdn dcPm) h14
  refine ⟨σ14, h, fun q b i hT hPp hPm => ?_, hsh14.trans (hsh13.trans (hsh12.trans
    (hsh11.trans hsh10))), hp14.trans (hp13.trans (hp12.trans (hp11.trans hp10))),
    fun i j t => (hf14 _ _ _ (bdn dPpPm)).trans ((f13 _ _ _ (fun h => dTPp h.symm)).trans
      ((f12 _ _ _ (fun h => dTPp h.symm)).trans (hPp11 i j t))), hPm14⟩
  rw [hf14 q b i (bdn hPm), f13 _ _ _ hT, f12 _ _ _ hT, f11 _ _ _ hPp, f10 _ _ _ hT]

/-- The trace of a node step's set-up: from a state whose block at offset $0$ of `Pp` holds
$\mathbf{P}$ and whose cell $2$ of `c` holds $h$, the block writes $\mathrm{tr}\,\mathbf{P}$ and
$\mathrm{fl}(\mathrm{tr}\,\mathbf{P} + h)$ in the cells $5$, $6$ of the scratch buffer `t`
(another buffer than `Pp` and `c`); only those cells change. -/
private theorem node_setup_trace (p : P) (k : ℕ) {t c Pp : ℕ} {st st' : St P K C}
    {Pm : Matrix (Fin k) (Fin k) (K × K)} {hv : K} (dPpt : Pp = t → False) (dct : c = t → False)
    (hP : pairLayout.Holds st.store p Pp 0 Pm) (hc2 : st.store.read p c 2 = some hv)
    (rest : Builder P ι ℕ ℕ Unit)
    (h : exec I (do
      ztraceRe p (.const k) Pp 0 ⟨t, 5⟩
      ins (.bin p .add ⟨t, 6⟩ ⟨t, 5⟩ ⟨c, 2⟩)
      rest : Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    ∃ σ : St P K C, exec I rest.run σ = some st' ∧
      (∀ q b i, (b ≠ t ∨ i ≠ 5 ∧ i ≠ 6) → σ.store.read q b i = st.store.read q b i) ∧
      σ.store.shape = st.store.shape ∧ σ.pos = st.pos ∧
      σ.store.read p t 6 = some (M.add (M.traceRe Pm) hv) := by
  intro M
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  obtain ⟨σ15, h15, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨htr15, hf15⟩ := read_of_exec_ztraceRe
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := st) (st' := σ15) hP (by
      simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
      exact Or.inl (Or.inl fun h => dPpt h.symm)) h15
  obtain ⟨hsh15, hp15⟩ := shape_pos_of_exec_ztraceRe_node p k h15
  have f15 : ∀ q b i, (b ≠ t ∨ i ≠ 5) → σ15.store.read q b i = st.store.read q b i := by
    intro q b i hb
    refine hf15 q b i ?_
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    change (b ≠ t ∨ i + 1 ≤ 5) ∨ 5 + 1 ≤ i
    omega
  rw [hr] at h
  obtain ⟨a7, a8, v6, s16, ha7, ha8, hv6, hw16, h⟩ := exists_of_exec_seq_bin h
  have e7 := Option.some_inj.mp (ha7.symm.trans htr15)
  subst e7
  change σ15.store.read p c 2 = some a8 at ha8
  rw [f15 _ _ _ (Or.inl dct), hc2, Option.some_inj] at ha8
  subst a8
  refine ⟨_, h, fun q b i hb => ?_, ?_, hp15, ?_⟩
  · change s16.read q b i = _
    rw [Store.read_of_write_eq_some_of_ne hw16 (hb.imp id fun h => h.2),
      f15 _ _ _ (hb.imp id fun h => h.1)]
  · change s16.shape = _
    rw [Store.shape_of_write_eq_some hw16, hsh15]
  · have e6 : M.add (M.traceRe Pm) hv = v6 := by
      change (I.sem.bin p .add (M.traceRe Pm) hv).getD default = v6
      rw [show I.sem.bin p .add (M.traceRe Pm) hv = some v6 from hv6, Option.getD_some]
    rw [e6]
    exact Store.read_of_write_eq_some hw16

/-- The distinct scratch buffers of a node step's set-up (stated as implications to `False`,
out of `omega`'s sight). -/
private theorem node_setup_ne {t sp W B T Pp Pm : ℕ} (hnd : [t, sp, W, B, T, Pp, Pm].Nodup) :
    (t = sp → False) ∧ (t = W → False) ∧ (t = B → False) ∧ (t = T → False) ∧
      (t = Pp → False) ∧ (t = Pm → False) ∧ (sp = W → False) ∧ (sp = B → False) ∧
      (W = B → False) ∧ (B = T → False) ∧ (B = Pp → False) ∧ (T = Pp → False) ∧
      (T = Pm → False) ∧ (Pp = Pm → False) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_⟩ <;> simp [h] at hnd

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
  obtain ⟨lMa, -, -, -, -, -, -, lLv, lpar, lSu, lc⟩ := hlt
  obtain ⟨gt, gsp, gW, gB, gT, gPp, gPm⟩ := hge
  obtain ⟨dtsp, dtW, dtB, dtT, dtPp, dtPm, dspW, dspB, dWB, dBT, dBPp, dTPp, dTPm, dPpPm⟩ :=
    node_setup_ne hnd
  obtain ⟨z0, o, -, hl1, -, -⟩ := id hflag
  obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
  have hMone : M.one = o := by
    change (I.sem.lit p 1).getD default = o; rw [hl1, Option.getD_some]
  obtain ⟨σA, hA', fA, shA, pA, tA0, tA1, tA4, hc1'⟩ := node_setup_scalars p n ℓ₀ d lo H
    (fun h => by omega) (fun h => by omega) hR hSu hc1 _ h
  have lA : ∀ q b i, b < s₀ → σA.store.read q b i = st.store.read q b i :=
    fun q b i hb => fA q b i fun h => by omega
  obtain ⟨σB, hB', fB, shB, pB, hBs⟩ := node_setup_sign hmm p hflag n F d lo k hk H
    (fun h => by omega) dtW (fun h => by omega) (fun h => by omega) (fun h => by omega)
    (fun h => by omega) (fun h => by omega) dspW dspB dWB
    (by rw [shA]; exact hB) (fun i j t => (lA _ _ _ lMa).trans (hA i j t)) tA4
    ((lA _ _ _ lpar).trans hpar) ((lA _ _ _ lc).trans hc1') ((lA _ _ _ lLv).trans hR) _ hA'
  have lB : ∀ q b i, b < s₀ → σB.store.read q b i = st.store.read q b i :=
    fun q b i hb => (fB q b i (fun h => by omega) (fun h => by omega) fun h => by omega).trans
      (lA q b i hb)
  obtain ⟨σC, hC', fC, shC, pC, hPp, hPm⟩ := node_setup_projectors p k dBT dBPp dTPp dTPm dPpPm
    (fun h => by omega) (fun h => by omega) (fun h => by omega) hBs
    ((lB _ _ _ lc).trans (hc0.trans hl1)) ((lB _ _ _ lc).trans hc1')
    ((lB _ _ _ lc).trans hc3) _ hB'
  have lC : ∀ q b i, b < s₀ → σC.store.read q b i = st.store.read q b i :=
    fun q b i hb => (fC q b i (fun h => by omega) (fun h => by omega) fun h => by omega).trans
      (lB q b i hb)
  obtain ⟨σD, hD', fD, shD, pD, tD6⟩ := node_setup_trace p k (fun h => dtPp h.symm)
    (fun h => by omega) hPp ((lC _ _ _ lc).trans hc2) _ hC'
  have tC : ∀ i, σC.store.read p t i = σA.store.read p t i := fun i =>
    (fC _ _ _ dtT dtPp dtPm).trans (fB _ _ _ dtW dtsp dtB)
  refine ⟨σD, hD', fun q b i hb => (fD q b i (Or.inl fun h => by omega)).trans (lC q b i hb),
    shD.trans (shC.trans (shB.trans shA)), pD.trans (pC.trans (pB.trans pA)),
    (fD _ _ _ (Or.inr ⟨by omega, by omega⟩)).trans ((tC 0).trans tA0),
    (fD _ _ _ (Or.inr ⟨by omega, by omega⟩)).trans ((tC 1).trans tA1), tD6,
    fun i j t' => (fD _ _ _ (Or.inl fun h => dtPp h.symm)).trans (hPp i j t'), ?_, hc1'⟩
  change pairLayout.Holds σD.store p Pm 0 (M.hermScale (M.negMat (M.hermShift B' M.one))
    (M.ofNat 2))
  rw [hMone]
  exact fun i j t' => (fD _ _ _ (Or.inl fun h => dtPm h.symm)).trans (hPm i j t')

end NLAlib
