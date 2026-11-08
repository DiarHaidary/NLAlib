/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode.NodeSuccess
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownLevel

/-!
# The downward level of the spectral bisection program succeeds

Under the standard model with every value in range, one level of the downward pass of
`NLAlib.eighProg` (`NLAlib.eighDownLevel`) succeeds from arenas that hold the nodes of its depth.

## Main results

* `NLAlib.exists_exec_eighDownLevel`: the level succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! #### Helpers of `NLAlib.exists_exec_eighDownLevel` -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL2: a mapped option is some when the option is. -/
theorem el2_map_ex {α β : Type} {o : Option α} {f : α → β} (h : ∃ a, o = some a) :
    ∃ b, o.map f = some b := by
  obtain ⟨a, ha⟩ := h
  exact ⟨f a, by rw [ha]; rfl⟩

omit [Inhabited K] in
/-- EL2: a sequence succeeds when its first part does and the rest succeeds from there. -/
private theorem el2_ex_seq {a b : Stmt P ι ℕ ℕ} {s s₁ : St P K C} (h₁ : exec I a s = some s₁)
    (h₂ : ∃ st', exec I b s₁ = some st') : ∃ st', exec I (.seq a b) s = some st' := by
  obtain ⟨t, ht⟩ := h₂
  exact ⟨t, by rw [exec_seq, h₁, Option.bind_some, ht]⟩

omit [Inhabited K] in
/-- EL2: a goal on a state, for a named state equal to it. -/
theorem el2_name {X : Stmt P ι ℕ ℕ} {s : St P K C}
    (h : ∀ σ : St P K C, σ = s → ∃ st', exec I X σ = some st') : ∃ st', exec I X s = some st' :=
  h s rfl

omit [Inhabited K] in
/-- EL2: an index literal, then the rest. -/
theorem el2_ex_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {v : K} {s' : Store P K} (hv : I.sem.lit p (e.eval : ℚ) = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some st') :
    ∃ st', exec I (.seq (.instr (.litIdx p dst e)) t) s = some st' := by
  rw [exec_seq_instr_litIdx I hv hw]
  exact h

omit [Inhabited K] in
/-- EL2: a binary operation, then the rest. -/
theorem el2_ex_bin {p : P} {b : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {a c v : K} {s' : Store P K} (hx : s.store.read p x.buf x.idx.eval = some a)
    (hy : s.store.read p y.buf y.idx.eval = some c) (hv : I.sem.bin p b a c = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p b) } = some st') :
    ∃ st', exec I (.seq (.instr (.bin p b dst x y)) t) s = some st' := by
  rw [exec_seq_instr_bin I hx hy hv hw]
  exact h

omit [Inhabited K] in
/-- EL2: a scoped index binder on a stored size within its bound. -/
private theorem el2_ex_bindIdx {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} {k : ℕ}
    (hr : ReadsIdx I.sem st.store p x.buf x.idx.eval k) (hk : k ≤ bound.eval)
    (h : ∃ st', exec I (body k) { st with cnt := st.cnt + I.charge (.toNat p) } = some st') :
    ∃ st', exec I (.seq (.bindIdx p x bound body) .skip) st = some st' := by
  unfold ReadsIdx at hr
  obtain ⟨w, hw, hv⟩ := Option.bind_eq_some_iff.mp hr
  rw [exec_seq_skip, exec_bindIdx_of_read I hw hv hk]
  exact h

omit [Inhabited K] in
/-- EL2: a loop of one iteration, then nothing. -/
private theorem el2_when1_eq {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s : St P K C}
    (he : e.eval = 1) : exec I (.seq (.loop e b) .skip) s = exec I (b 0) s := by
  rw [exec_seq_skip, exec_loop, he]
  simp [List.range_one]

omit [Inhabited K] in
/-- EL2: a loop of no iteration, then nothing. -/
private theorem el2_when0_eq {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s : St P K C}
    (he : e.eval = 0) : exec I (.seq (.loop e b) .skip) s = some s := by
  rw [exec_seq_skip, exec_loop, he]
  rfl

omit [Inhabited K] in
/-- EL2: a loop of one iteration that succeeds. -/
private theorem el2_ex_when1 {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s : St P K C}
    (he : e.eval = 1) (h : ∃ st', exec I (b 0) s = some st') :
    ∃ st', exec I (.seq (.loop e b) .skip) s = some st' := by
  rw [el2_when1_eq he]
  exact h

omit [Inhabited K] in
/-- EL2: a guarded block, then the rest. -/
private theorem el2_ex_whenBind {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {s σ : St P K C}
    (h₁ : exec I (eighWhen e b).run s = some σ) (h₂ : ∃ st', exec I (f ()).run σ = some st') :
    ∃ st', exec I (eighWhen e b >>= f).run s = some st' := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl), h₁, Option.bind_some]
  exact h₂

omit [Inhabited K] in
/-- EL2: a conditional on a comparison of stored cells, then nothing. -/
private theorem el2_ex_ite {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {t e : Stmt P ι ℕ ℕ}
    {st : St P K C} {a b : K} {r : Bool} (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some b) (hc : I.sem.cmp p c a b = some r)
    (h : ∃ st', (if r then exec I t { st with cnt := st.cnt + I.charge (.cmp p) }
      else exec I e { st with cnt := st.cnt + I.charge (.cmp p) }) = some st') :
    ∃ st', exec I (.seq (.ite p c x y t e) .skip) st = some st' := by
  rw [exec_seq_skip, exec_ite]
  simp only [cmpStep, hx, hy, hc, Option.bind_some, Option.map_some]
  exact h

/-- EL2: an arithmetic operation of the standard model succeeds, with its rounding. -/
theorem el2_bin {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) {b : BinOp} (hb : b.IsArith)
    {x y : K} (hy : b = .div → dec p y ≠ 0) :
    ∃ z, I.sem.bin p b x y = some z ∧
      ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = b.realOp (dec p x) (dec p y) * (1 + δ) := by
  obtain ⟨z, hz⟩ := hsem.bin_ok p b x y hb hy trivial
  exact ⟨z, hz, hsem.bin_err p b x y z hb hz⟩

omit [Inhabited K] in
/-- EL2: a literal into a cell of a buffer, then nothing, succeeds and keeps the other buffers. -/
private theorem el2_body_lit {p : P} {Y len : ℕ} {i : IExp ℕ} {q₀ : ℚ} {s : St P K C}
    (hz : ∃ z, I.sem.lit p q₀ = some z) (hY : s.store.shape[Y]? = some (p, len))
    (hi : i.eval < len) :
    ∃ s', exec I (.seq (.instr (.lit p ⟨Y, i⟩ q₀)) .skip) s = some s' ∧
      s'.store.shape = s.store.shape ∧ ∀ q b j, b ≠ Y → s'.store.read q b j = s.store.read q b j := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s', hw⟩ := Store.exists_write_eq_some_of_getElem?_shape z hY hi
  refine ⟨_, (exec_seq_instr_lit I hz hw).trans (exec_skip I _), Store.shape_of_write_eq_some hw,
    fun q b j hb => Store.read_of_write_eq_some_of_ne hw (Or.inl hb)⟩

omit [Inhabited K] in
/-- EL2: a copy into a cell of a buffer, then nothing, succeeds and keeps the other buffers. -/
private theorem el2_body_copy {p : P} {Y len : ℕ} {i : IExp ℕ} {src : Cell ℕ ℕ} {s : St P K C}
    (hx : ∃ v, s.store.read p src.buf src.idx.eval = some v)
    (hY : s.store.shape[Y]? = some (p, len)) (hi : i.eval < len) :
    ∃ s', exec I (.seq (.instr (.copy p ⟨Y, i⟩ src)) .skip) s = some s' ∧
      s'.store.shape = s.store.shape ∧ ∀ q b j, b ≠ Y → s'.store.read q b j = s.store.read q b j := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨s', hw⟩ := Store.exists_write_eq_some_of_getElem?_shape v hY hi
  refine ⟨_, (exec_seq_instr_copy I hv hw).trans (exec_skip I _), Store.shape_of_write_eq_some hw,
    fun q b j hb => Store.read_of_write_eq_some_of_ne hw (Or.inl hb)⟩

omit [Inhabited K] in
/-- EL2: a loop whose steps succeed, keeping the shape and the buffers other than `Y`. -/
private theorem el2_loop {m : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {Y : ℕ} {st : St P K C}
    (hstep : ∀ w < m.eval, ∀ s : St P K C, s.store.shape = st.store.shape →
      (∀ q b j, b ≠ Y → s.store.read q b j = st.store.read q b j) →
      ∃ s', exec I (body w) s = some s' ∧ s'.store.shape = s.store.shape ∧
        ∀ q b j, b ≠ Y → s'.store.read q b j = s.store.read q b j) :
    ∃ st', exec I (.loop m body) st = some st' ∧ st'.store.shape = st.store.shape ∧
      ∀ q b j, b ≠ Y → st'.store.read q b j = st.store.read q b j := by
  obtain ⟨st', h, hR⟩ := exists_exec_loop_eq_some_of_forall I (fun _ (s : St P K C) =>
    s.store.shape = st.store.shape ∧
      ∀ q b j, b ≠ Y → s.store.read q b j = st.store.read q b j) ⟨rfl, fun _ _ _ _ => rfl⟩
    (fun w hw s ⟨hs, hf⟩ => by
      obtain ⟨s', h', hs', hf'⟩ := hstep w hw s hs hf
      exact ⟨s', h', hs'.trans hs, fun q b j hb => (hf' q b j hb).trans (hf q b j hb)⟩) (st := st)
  exact ⟨st', h, hR⟩

/-- EL2: a leaf succeeds when its blocks are allocated and its matrix is stored. -/
private theorem el2_leaf_ex {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (diag : Bool) (k : ℕ)
    {Ma Ua Ea : ℕ} {mo uo eo : IExp ℕ} {kd : Cell ℕ ℕ} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {lU lE lK : ℕ}
    (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (hUa : st.store.shape[Ua]? = some (p, lU)) (hU : uo.eval + 2 * (k * k) ≤ lU)
    (hEa : st.store.shape[Ea]? = some (p, lE)) (hE : eo.eval + k ≤ lE)
    (hKd : st.store.shape[kd.buf]? = some (p, lK)) (hK : kd.idx.eval < lK)
    (hMaUa : Ma ≠ Ua) (hMaEa : Ma ≠ Ea) :
    ∃ st', exec I (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd).run st =
      some st' := by
  have hii : ∀ i < k, 2 * (i + k * i) + 2 ≤ 2 * (k * k) := fun i hi => by nlinarith
  have hz0 := hsem.lit_ok p 0 trivial
  have hz1 := hsem.lit_ok p 1 trivial
  obtain ⟨z1', hz1'⟩ := hsem.lit_ok p ((1 : ℕ) : ℚ) trivial
  obtain ⟨s1, h1, sh1, fr1⟩ := el2_loop (Y := Ua) (st := st) (m := 2 * (IExp.const k * IExp.const k))
    (body := fun w => .seq (.instr (.lit p ⟨Ua, uo + .var w⟩ 0)) .skip)
    (fun w hw s hs _ => el2_body_lit hz0 (by rw [hs]; exact hUa) (by
      change uo.eval + w < lU
      change w < 2 * (k * k) at hw
      omega))
  obtain ⟨s2, h2, sh2, fr2⟩ := el2_loop (Y := Ua) (st := s1) (m := IExp.const k)
    (body := fun i => .seq (.instr (.lit p ⟨Ua, uo + zidx (.const k) (.var i) (.var i)⟩ 1)) .skip)
    (fun i hi s hs _ => el2_body_lit hz1 (by rw [hs, sh1]; exact hUa) (by
      change uo.eval + 2 * (i + k * i) < lU
      change i < k at hi
      have := hii i hi
      omega))
  have hMa2 : ∀ i < k, ∃ v, s2.store.read p Ma (mo.eval + 2 * (i + k * i)) = some v := by
    intro i hi
    rw [fr2 _ _ _ hMaUa, fr1 _ _ _ hMaUa]
    exact ⟨_, hA ⟨i, hi⟩ ⟨i, hi⟩ ⟨0, two_pos⟩⟩
  obtain ⟨s3, h3, sh3, fr3⟩ := el2_loop (Y := Ea) (st := s2) (m := IExp.const k)
    (body := fun i => ((if diag then Builder.ins (ι := ι) (.copy p ⟨Ea, eo + .var i⟩
        ⟨Ma, mo + zidx (.const k) (.var i) (.var i)⟩)
      else Builder.ins (.lit p ⟨Ea, eo + .var i⟩ 0)) : Builder P ι ℕ ℕ Unit).run)
    (fun i hi s hs hf => by
      change i < k at hi
      cases diag
      · exact el2_body_lit hz0 (by rw [hs, sh2, sh1]; exact hEa) (by change eo.eval + i < lE; omega)
      · refine el2_body_copy ?_ (by rw [hs, sh2, sh1]; exact hEa) (by
          change eo.eval + i < lE; omega)
        obtain ⟨v, hv⟩ := hMa2 i hi
        exact ⟨v, (hf _ _ _ hMaEa).trans hv⟩)
  obtain ⟨s4, hw4⟩ := Store.exists_write_eq_some_of_getElem?_shape z1'
    (by rw [sh3, sh2, sh1]; exact hKd) hK
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) .skip)))
    (.seq (.loop _ _) (.seq (.instr (.litIdx p kd 1)) .skip))) st = some st'
  refine el2_ex_seq (s₁ := s2) ?_ (el2_ex_seq h3
    ⟨_, (exec_seq_instr_litIdx I (v := z1') hz1' hw4).trans (exec_skip I _)⟩)
  rw [exec_named]
  exact (exec_seq_of_exec_eq_some I h1).trans ((exec_seq_of_exec_eq_some I h2).trans
    (exec_skip I _))

/-- EL2: the windows of the levels decode to positive values from a positive $R_0$ and to $0$
from a zero $R_0$. -/
private theorem el2_lp {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (hlit : IsExactIntLit dec I.sem 2) {R₀ ε : K} {ℓ₀ : ℕ} (hℓ : 1 ≤ ℓ₀) :
    ∀ d, (0 < dec p R₀ → 0 < dec p (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1) ∧
      (dec p R₀ = 0 → dec p (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1 = 0) := by
  have hpos : ∀ {δ : ℝ}, |δ| ≤ u p → 0 < 1 + δ := fun h => by
    have := (abs_le.mp h).1; linarith
  obtain ⟨one, hone, hone'⟩ := hlit p 1 (by omega)
  obtain ⟨two, htwo, htwo'⟩ := hlit p 2 (by omega)
  simp only [Nat.cast_one] at hone hone'
  push_cast at htwo'
  intro d
  induction d with
  | zero => exact ⟨id, id⟩
  | succ d ih =>
    obtain ⟨L, hL⟩ := hsem.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) trivial
    obtain ⟨δL, hδL, hLd⟩ := hsem.lit_err p _ L hL
    have hLpos : 0 < dec p L := by
      rw [hLd]
      have hx : (0 : ℝ) < (((ℓ₀ + d : ℕ) : ℚ) : ℝ) := by
        exact_mod_cast (show 0 < ℓ₀ + d by omega)
      exact mul_pos hx (hpos hδL)
    obtain ⟨h1, hh1, δ1, hδ1, hd1⟩ := el2_bin hsem p (b := .div) trivial (x := one) (y := two)
      (fun _ => by rw [htwo']; norm_num)
    obtain ⟨h2, hh2, δ2, hδ2, hd2⟩ := el2_bin hsem p (b := .div) trivial (x := two) (y := L)
      (fun _ => ne_of_gt hLpos)
    obtain ⟨h3, hh3, δ3, hδ3, hd3⟩ := el2_bin hsem p (b := .add) trivial (x := h1) (y := h2)
      (fun h => by cases h)
    obtain ⟨h4, hh4, δ4, hδ4, hd4⟩ := el2_bin hsem p (b := .mul) trivial (x := h3)
      (y := (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1) (fun h => by cases h)
    have e : (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).1 = h4 := by
      change (I.sem.bin p .mul ((I.sem.bin p .add ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default) ((I.sem.bin p .div
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default) ((I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD
        default)).getD default)).getD default) _).getD default = h4
      rw [hone, htwo, hL]
      simp only [Option.getD_some]
      rw [hh1, Option.getD_some, hh2, Option.getD_some, hh3, Option.getD_some, hh4,
        Option.getD_some]
    have hX : 0 < dec p h3 := by
      simp only [BinOp.realOp] at hd1 hd2 hd3
      rw [hd3, hd1, hd2, hone', htwo']
      have := hpos hδ1; have := hpos hδ2; have := hpos hδ3
      have : 0 < 2 / dec p L := by positivity
      positivity
    simp only [BinOp.realOp] at hd4
    rw [e, hd4]
    have := hpos hδ4
    exact ⟨fun h => by have := ih.1 h; positivity, fun h => by rw [ih.2 h]; ring⟩

/-- EL2: the semantics decides flags. -/
theorem el2_flags {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) {B : ℕ}
    (hlit : IsExactIntLit dec I.sem B) (hB : 1 ≤ B) (p : P) : I.sem.DecidesFlags p := by
  obtain ⟨z, hz, hzd⟩ := hlit p 0 (by omega)
  obtain ⟨o, ho, hod⟩ := hlit p 1 hB
  simp only [Nat.cast_zero, Nat.cast_one] at hz hzd ho hod
  refine ⟨z, o, hz, ho, ?_, ?_⟩
  · rw [hsem.cmp_eq, hzd, hod]; simp
  · rw [hsem.cmp_eq]; simp

omit [Inhabited K] in
/-- EL2: a slot that starts no node succeeds. -/
private theorem el2_slot_skip_ex {p : P} {mm qr : ι}
    {n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo : ℕ} {s : St P K C}
    (hSz : ReadsIdx I.sem s.store p Sz (n * d + lo) 0) :
    ∃ s', exec I (el1_slotBody p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo).run s =
      some s' := by
  unfold el1_slotBody
  refine el2_ex_bindIdx (k := 0) (by exact hSz) (Nat.zero_le _) ?_
  exact ⟨_, el2_when0_eq (by change 1 - (1 - 0) = 0; omega)⟩

set_option maxHeartbeats 1600000 in
-- The slot unfolds the binder, two guards, the window test and the node step.
/-- EL2: the slot of a node of depth $d$ succeeds; a node step's window is positive since its
window test failed. -/
private theorem el2_slot_node_ex {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hℓ : 1 ≤ ℓ₀ + d) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c t lo : ℕ} {s : St P K C}
    {R₀ β : K} {y : EighNode K} (hk1 : 1 ≤ y.k) (hkn : lo + y.k ≤ n)
    (hH : H.Shaped s.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (ht : t ∉ H.handles ++ [par, c]) (ht4 : ∃ len, s.store.shape[t]? = some (p, len) ∧ 4 < len)
    (hSz : ReadsIdx I.sem s.store p H.Sz (n * d + lo) y.k)
    (hA : pairLayout.Holds s.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A)
    (hR : s.store.read p H.Lv (2 * d) = some y.R) (hR₀ : 0 ≤ dec p R₀)
    (hRpos : 0 < dec p R₀ → 0 < dec p y.R) (hRz : dec p R₀ = 0 → dec p y.R = 0)
    (hε : s.store.read p H.Lv (2 * d + 1) = some y.ε)
    (hpar : s.store.read p par 0 = some R₀ ∧ s.store.read p par 2 = some β)
    (hSu : 2 ≤ y.k → (∃ v, s.store.read p Su lo = some v) ∧ (Su = t → lo ≠ 4))
    (hSg : 2 ≤ y.k → (∀ w < 4 * (n * n), ∃ v, s.store.read p Sg w = some v) ∧ Sg ≠ t)
    (hc : s.store.read p c 0 = I.sem.lit p 1 ∧ s.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      (∃ v, s.store.read p c 2 = some v) ∧ (∃ v, s.store.read p c 3 = some v) ∧
      s.store.read p c 4 = some (I.sem.sqrtHalf p)) :
    ∃ s', exec I (el1_slotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c t lo).run s = some s' := by
  have dUaMa : H.Ua ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dEaMa : H.Ea ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dtLv : H.Lv ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtMa : H.Ma ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtpar : par ≠ t := fun h => ht (by simp [h])
  have dtc : c ≠ t := fun h => ht (by simp [h])
  obtain ⟨-, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
  have e5 : 2 * n * lo + 2 * (n * y.k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) hkn
    nlinarith
  have e6 : 2 * (n * n) * d + 2 * (n * n) ≤ 2 * (n * n) * (D + 1) := by
    have := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ D + 1 by omega)
    nlinarith
  have e7 : n * d + n ≤ n * D := by
    have := Nat.mul_le_mul_left n (show d + 1 ≤ D by omega)
    nlinarith
  have e8 : n * D ≤ n * (D + 1) := Nat.mul_le_mul_left n (by omega)
  -- a leaf, from a state with the shape of `s` and the node's matrix stored
  have hleaf : ∀ (diag : Bool) (σ : St P K C), σ.store.shape = s.store.shape →
      pairLayout.Holds σ.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A →
      ∃ σ', exec I (eighLeafBlock (ι := ι) p diag (.var y.k) H.Ma
        (eighBlockOff (.const n) (.const d) (.var lo)) H.Ua
        (eighBlockOff (.const n) (.const d) (.var lo)) H.Ea
        (eighSlotOff (.const n) (.const d) (.var lo))
        ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩).run σ = some σ' := by
    intro diag σ hσ hAσ
    obtain ⟨σ', h'⟩ := el2_leaf_ex hsem p diag y.k (A := y.A) (st := σ) (Ma := H.Ma)
      (Ua := H.Ua) (Ea := H.Ea) (mo := eighBlockOff (.const n) (.const d) (.var lo))
      (uo := eighBlockOff (.const n) (.const d) (.var lo))
      (eo := eighSlotOff (.const n) (.const d) (.var lo))
      (kd := ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) (by exact hAσ)
      (by rw [hσ]; exact hUa) (by change 2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ _; omega)
      (by rw [hσ]; exact hEa) (by change n * d + lo + y.k ≤ _; omega)
      (by rw [hσ]; exact hKd) (by change n * d + lo < _; omega)
      (fun h => dUaMa h.symm) (fun h => dEaMa h.symm)
    exact ⟨σ', (el1_leaf_congr p diag y.k H.Ma H.Ua H.Ea _ _ _ _ _).trans h'⟩
  unfold el1_slotBody
  refine el2_ex_bindIdx (k := y.k) (by exact hSz) (by change y.k ≤ n - lo; omega) ?_
  refine el2_ex_when1 (by change 1 - (1 - y.k) = 1; omega) ?_
  rcases Nat.lt_or_ge y.k 2 with hk | hk
  · obtain ⟨σ', h'⟩ := hleaf true { s with cnt := s.cnt + I.charge (.toNat p) } rfl hA
    refine el2_ex_whenBind (σ := σ') ?_ ?_
    · exact (el2_when1_eq (e := 1 - (1 - (1 - (IExp.var y.k - 1))))
        (by change 1 - (1 - (1 - (y.k - 1))) = 1; omega)).trans h'
    · exact ⟨_, el2_when0_eq (by change 1 - (1 - (y.k - 1)) = 0; omega)⟩
  · refine el2_ex_whenBind (el2_when0_eq (by change 1 - (1 - (1 - (y.k - 1))) = 0; omega)) ?_
    refine el2_ex_when1 (by change 1 - (1 - (y.k - 1)) = 1; omega) ?_
    obtain ⟨len, htsh, hlen⟩ := ht4
    obtain ⟨v, hv, δ, hδ, hvd⟩ := el2_bin hsem p (b := .mul) trivial (x := y.ε) (y := R₀)
      (fun h => by cases h)
    obtain ⟨s₂, hw2⟩ := Store.exists_write_eq_some_of_getElem?_shape v htsh hlen
    have hr2 : ∀ q b i, ¬ (b = t ∧ i = 4) → s₂.read q b i = s.store.read q b i :=
      fun q b i hne => Store.read_of_write_eq_some_of_ne hw2 (not_and_or.mp hne)
    have hsh2 : s₂.shape = s.store.shape := Store.shape_of_write_eq_some hw2
    have hA2 : pairLayout.Holds s₂ p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A :=
      el1_holds_keep hA fun i _ _ => hr2 _ _ _ fun h => dtMa h.1
    refine el2_ex_bin (s' := s₂) (by exact hε) (by exact hpar.1) hv (by exact hw2) ?_
    change ∃ st', exec I (.seq (.ite _ _ _ _ _ _) .skip) _ = some st'
    refine el2_ex_ite (a := y.R) (b := v) (by exact (hr2 _ _ _ fun h => dtLv h.1).trans hR)
      (by exact Store.read_of_write_eq_some hw2) (hsem.cmp_le p y.R v) ?_
    by_cases hle : dec p y.R ≤ dec p v
    · rw [if_pos (decide_eq_true hle)]
      exact hleaf false _ hsh2 hA2
    · rw [if_neg (by simpa using hle)]
      have hRp : 0 < dec p y.R := by
        rcases hR₀.lt_or_eq with h | h
        · exact hRpos h
        · exfalso
          apply hle
          rw [hRz h.symm, hvd, ← h]
          simp [BinOp.realOp]
      obtain ⟨hSu1, hSu2⟩ := hSu hk
      obtain ⟨hSg1, hSg2⟩ := hSg hk
      obtain ⟨sN, hN⟩ := exists_exec_eighNodeBlock hmm hqr hsem
        (fun p k hk => hlit p k (by omega)) htn p hu n ℓ₀ F d lo y.k
        (fun p k hk => hlit p k (by omega)) hkn hk hℓ H (A := y.A)
        (R := y.R) (β := β) (st := { s with store := s₂, cnt := _ }) hd
        (el1_shaped_of_eq (fun b _ => by change s₂.shape[b]? = _; rw [hsh2]) hH) hbufs hA2
        ((hr2 _ _ _ fun h => dtLv h.1).trans hR) hRp
        ((hr2 _ _ _ fun h => dtpar h.1).trans hpar.2)
        (by obtain ⟨w, hw⟩ := hSu1; exact ⟨w, (hr2 _ _ _ fun h => hSu2 h.1 h.2).trans hw⟩)
        (fun w hw => by
          obtain ⟨x, hx⟩ := hSg1 w hw
          exact ⟨x, (hr2 _ _ _ fun h => hSg2 h.1).trans hx⟩)
        ⟨(hr2 _ _ _ fun h => dtc h.1).trans hc.1, (hr2 _ _ _ fun h => dtc h.1).trans hc.2.1,
          by obtain ⟨x, hx⟩ := hc.2.2.1; exact ⟨x, (hr2 _ _ _ fun h => dtc h.1).trans hx⟩,
          by obtain ⟨x, hx⟩ := hc.2.2.2.1; exact ⟨x, (hr2 _ _ _ fun h => dtc h.1).trans hx⟩,
          (hr2 _ _ _ fun h => dtc h.1).trans hc.2.2.2.2⟩
      exact ⟨sN, (el1_node_congr p mm qr n ℓ₀ F d lo y.k par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp c
        _).trans hN⟩

set_option maxHeartbeats 1600000 in
-- The run unfolds the scope, seven instructions, two draw loops and the loop over the slots.
/-- One level of the downward pass succeeds under the standard model at $u$ with every value in
range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor conversion, if the
kernels are routines on pairs, $\ell_0 \ge 1$, $\varepsilon$ and $R_0$ decode to nonnegative values
and the arenas hold the nodes of depth $d$ (hypotheses as `NLAlib.holds_of_exec_eighDownLevel`, with
its tape positions and constants). No printed source. -/
theorem exists_exec_eighDownLevel {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hℓ : 1 ≤ ℓ₀) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hSu : ∃ len, st.store.shape[Su]? = some (p, len) ∧ n ≤ len)
    (hSg : ∃ len, st.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su
      Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st = some st' := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hlev1, hlev2, hlev3, hlev4⟩ := hlev
  set tH := st.store.size with htH
  set S0 : Store P K := st.store.push (p, Array.replicate (5 : IExp ℕ).eval none) with hS0
  have hflag : I.sem.DecidesFlags p := el2_flags hsem hlit (by omega) p
  have hcmp := hsem.cmp_le p
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  obtain ⟨z0, o1, -, hl1, -, -⟩ := id hflag
  have lpar := Store.lt_size_of_read_eq_some hpar.1
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans hl1)
  have lMa := hsz hMa
  have lUa := hsz hUa
  have lQa := hsz hQa
  have lEa := hsz hEa
  have lSz := hsz hSzs
  have lKd := hsz hKd
  have lKp := hsz hKp
  have lLv := hsz hLv
  have dLvc : H.Lv ≠ c := fun h => by simp [EighArenas.handles, h] at hbufs
  have dLvSu : H.Lv ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dLvSg : H.Lv ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzSu : H.Sz ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzSg : H.Sz ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzLv : H.Sz ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSu : H.Ma ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSg : H.Ma ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaLv : H.Ma ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSu : par ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSg : par ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparLv : par ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSu : c ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSg : c ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSuSg : Su ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have hpb : par ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hcb : c ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hSub : Su ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hSgb : Sg ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hLvb : H.Lv ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hnd
  have hwinb : ∀ {lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}, el1_win H n d lo k cs b i →
      b < st.store.size := fun hw => by
    have := el1_win_buf hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hr0 : ∀ q b i, b < tH → S0.read q b i = st.store.read q b i :=
    fun q b i hb => Store.read_push_of_lt hb
  have dcT : c ≠ tH := by omega
  have dLvT : H.Lv ≠ tH := by omega
  have hS0sz : S0.size = tH + 1 := by rw [hS0, Array.size_push, htH]
  have hshape5 : S0.shape[tH]? = some (p, 5) := Store.getElem?_shape_push_size _ _ _
  have hLvsh : S0.shape[H.Lv]? = some (p, 2 * (D + 1)) := by
    rw [hS0, Store.getElem?_shape_push_of_lt _ lLv]; exact hLv
  have hpos1 : ∀ {δ : ℝ}, |δ| ≤ u p → 0 < 1 + δ := fun h => by
    have := (abs_le.mp h).1; linarith
  -- the values of the seven instructions
  obtain ⟨tw, htw, -⟩ := hlit p 2 (by omega)
  obtain ⟨v0, hv0'⟩ := hsem.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) trivial
  have hv0pos : 0 < dec p v0 := by
    obtain ⟨δ, hδ, hvd⟩ := hsem.lit_err p _ v0 hv0'
    rw [hvd]
    have hx : (0 : ℝ) < (((ℓ₀ + d : ℕ) : ℚ) : ℝ) := by
      exact_mod_cast (show 0 < ℓ₀ + d by omega)
    exact mul_pos hx (hpos1 hδ)
  obtain ⟨v1, hv1, -⟩ := el2_bin hsem p (b := .div) trivial (x := tw) (y := v0)
    (fun _ => ne_of_gt hv0pos)
  obtain ⟨v2, hv2, -⟩ := el2_bin hsem p (b := .add) trivial (x := M.div M.one (M.ofNat 2))
    (y := v1) (fun h => by cases h)
  obtain ⟨v3, hv3, -⟩ := el2_bin hsem p (b := .mul) trivial (x := v2)
    (y := (eighLevelParams M R₀ ε ℓ₀ d).1) (fun h => by cases h)
  obtain ⟨v4, hv4, -⟩ := el2_bin hsem p (b := .div) trivial (x := o1) (y := v0)
    (fun _ => ne_of_gt hv0pos)
  obtain ⟨v5, hv5, -⟩ := el2_bin hsem p (b := .sub) trivial (x := o1) (y := v4)
    (fun h => by cases h)
  obtain ⟨v6, hv6, -⟩ := el2_bin hsem p (b := .mul) trivial (x := v5)
    (y := (eighLevelParams M R₀ ε ℓ₀ d).2) (fun h => by cases h)
  obtain ⟨S1, hw0'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) v0 hshape5
    (by norm_num)
  have sh1 : S1.shape = S0.shape := Store.shape_of_write_eq_some hw0'
  obtain ⟨S2, hw1'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2) v1
    (by rw [sh1]; exact hshape5) (by norm_num)
  have sh2 : S2.shape = S0.shape := (Store.shape_of_write_eq_some hw1').trans sh1
  obtain ⟨S3, hw2'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 3) v2
    (by rw [sh2]; exact hshape5) (by norm_num)
  have sh3 : S3.shape = S0.shape := (Store.shape_of_write_eq_some hw2').trans sh2
  obtain ⟨S4, hw3'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2 * (d + 1)) v3
    (by rw [sh3]; exact hLvsh) (by omega)
  have sh4 : S4.shape = S0.shape := (Store.shape_of_write_eq_some hw3').trans sh3
  obtain ⟨S5, hw4'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) v4
    (by rw [sh4]; exact hshape5) (by norm_num)
  have sh5 : S5.shape = S0.shape := (Store.shape_of_write_eq_some hw4').trans sh4
  obtain ⟨S6, hw5'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 3) v5
    (by rw [sh5]; exact hshape5) (by norm_num)
  have sh6 : S6.shape = S0.shape := (Store.shape_of_write_eq_some hw5').trans sh5
  obtain ⟨S7, hw6'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2 * (d + 1) + 1) v6
    (by rw [sh6]; exact hLvsh) (by omega)
  -- the reads of the seven instructions
  have ea1 : S1.read p c 1 = st.store.read p c 1 := by
    rw [Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have ea2 : S2.read p c 2 = st.store.read p c 2 := by
    rw [Store.read_of_write_eq_some_of_ne hw1' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have eb3 : S3.read p H.Lv (2 * d) = st.store.read p H.Lv (2 * d) := by
    rw [Store.read_of_write_eq_some_of_ne hw2' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dLvT), hr0 _ _ _ lLv]
  have ea4 : S4.read p c 0 = st.store.read p c 0 := by
    rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inl dLvc.symm),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have eb4 : S4.read p tH 0 = some v0 := by
    rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inl dLvT.symm),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inr (by omega)),
      Store.read_of_write_eq_some hw0']
  have ea5 : S5.read p c 0 = st.store.read p c 0 := by
    rw [Store.read_of_write_eq_some_of_ne hw4' (Or.inl dcT), ea4]
  have eb6 : S6.read p H.Lv (2 * d + 1) = st.store.read p H.Lv (2 * d + 1) := by
    rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dLvT), hr0 _ _ _ lLv]
  have r1a : S1.read p c 1 = some tw := ea1.trans (hc.2.1.trans htw)
  have r1b : S1.read p tH 0 = some v0 := Store.read_of_write_eq_some hw0'
  have r2a : S2.read p c 2 = some (M.div M.one (M.ofNat 2)) := ea2.trans hc.2.2.1
  have r2b : S2.read p tH 2 = some v1 := Store.read_of_write_eq_some hw1'
  have r3a : S3.read p tH 3 = some v2 := Store.read_of_write_eq_some hw2'
  have r3b : S3.read p H.Lv (2 * d) = some (eighLevelParams M R₀ ε ℓ₀ d).1 := eb3.trans hlev3
  have r4a : S4.read p c 0 = some o1 := ea4.trans (hc.1.trans hl1)
  have r5a : S5.read p c 0 = some o1 := ea5.trans (hc.1.trans hl1)
  have r5b : S5.read p tH 1 = some v4 := Store.read_of_write_eq_some hw4'
  have r6a : S6.read p tH 3 = some v5 := Store.read_of_write_eq_some hw5'
  have r6b : S6.read p H.Lv (2 * d + 1) = some (eighLevelParams M R₀ ε ℓ₀ d).2 :=
    eb6.trans hlev4
  -- the frame of the seven instructions
  have hr7 : ∀ q b i, b < tH → ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      S7.read q b i = st.store.read q b i := by
    intro q b i hb hL
    have hbT : b ≠ tH := by omega
    have hL' : b ≠ H.Lv ∨ (i ≠ 2 * (d + 1) ∧ i ≠ 2 * (d + 1) + 1) := by
      by_cases h' : b = H.Lv
      · exact Or.inr ⟨fun h'' => hL ⟨h', Or.inl h''⟩, fun h'' => hL ⟨h', Or.inr h''⟩⟩
      · exact Or.inl h'
    rw [Store.read_of_write_eq_some_of_ne hw6' (hL'.imp_right And.right),
      Store.read_of_write_eq_some_of_ne hw5' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw3' (hL'.imp_right And.left),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl hbT), hr0 _ _ _ hb]
  have hsh7 : S7.shape = S0.shape := by
    rw [Store.shape_of_write_eq_some hw6', Store.shape_of_write_eq_some hw5',
      Store.shape_of_write_eq_some hw4', Store.shape_of_write_eq_some hw3',
      Store.shape_of_write_eq_some hw2', Store.shape_of_write_eq_some hw1',
      Store.shape_of_write_eq_some hw0']
  -- the run of the parameters
  change ∃ st', exec I (.seq (.alloc p _ _) .skip) st = some st'
  rw [exec_seq_skip, exec_alloc]
  refine el2_map_ex ?_
  refine el2_ex_litIdx (by exact hv0') (by exact hw0') ?_
  refine el2_ex_bin (by exact r1a) (by exact r1b) hv1 (by exact hw1') ?_
  refine el2_ex_bin (by exact r2a) (by exact r2b) hv2 (by exact hw2') ?_
  refine el2_ex_bin (by exact r3a) (by exact r3b) hv3 (by exact hw3') ?_
  refine el2_ex_bin (by exact r4a) (by exact eb4) hv4 (by exact hw4') ?_
  refine el2_ex_bin (by exact r5a) (by exact r5b) hv5 (by exact hw5') ?_
  refine el2_ex_bin (by exact r6a) (by exact r6b) hv6 (by exact hw6') ?_
  refine el2_name fun σ7 hσ7 => ?_
  have h7s : σ7.store = S7 := by rw [hσ7]
  have h7p : σ7.pos = st.pos := by rw [hσ7]
  -- the draws
  obtain ⟨len1, hSush, hlen1⟩ := hSu
  obtain ⟨len2, hSgsh, hlen2⟩ := hSg
  have lSu : Su < tH := hsz hSush
  have lSg : Sg < tH := hsz hSgsh
  have hS7Su : S7.shape[Su]? = some (p, len1) := by
    rw [hsh7, hS0, Store.getElem?_shape_push_of_lt _ lSu]; exact hSush
  have hS7Sg : S7.shape[Sg]? = some (p, len2) := by
    rw [hsh7, hS0, Store.getElem?_shape_push_of_lt _ lSg]; exact hSgsh
  obtain ⟨σu, hdu, -⟩ := exec_forRange_draw I p .uniform Su 0 (.const n) (fun i => .var i)
    (fun i => (Nat.zero_add i).symm) σ7 (fun i hi => ⟨_,
      Store.exists_write_eq_some_of_getElem?_shape (I.tape .uniform 0) (by rw [h7s]; exact hS7Su)
        (by change i < n at hi; omega)⟩)
  have hu' : exec I (.loop (.const n) fun i =>
      (Builder.ins (ι := ι) (.draw p .uniform ⟨Su, .var i⟩)).run) σ7 = some σu :=
    (exec_seq_skip I _ _).symm.trans hdu
  refine el2_ex_seq hu' ?_
  obtain ⟨hush, hupos, hurd, hufr⟩ := el1_draw_loop hu'
  obtain ⟨σg, hg, -⟩ := exec_forRange_draw I p .gaussian Sg 0 (4 * (IExp.const n * IExp.const n))
    (fun w => .var w) (fun w => (Nat.zero_add w).symm) σu (fun w hw => ⟨_,
      Store.exists_write_eq_some_of_getElem?_shape (I.tape .gaussian 0)
        (by rw [hush, h7s]; exact hS7Sg) (by change w < 4 * (n * n) at hw; omega)⟩)
  have hg' : exec I (.loop (4 * (IExp.const n * IExp.const n)) fun w =>
      (Builder.ins (ι := ι) (.draw p .gaussian ⟨Sg, .var w⟩)).run) σu = some σg :=
    (exec_seq_skip I _ _).symm.trans hg
  refine el2_ex_seq hg' ?_
  obtain ⟨hgsh, hgpos, hgrd, hgfr⟩ := el1_draw_loop hg'
  have hshg : σg.store.shape = S0.shape := by rw [hgsh, hush, h7s, hsh7]
  have hSuR : ∀ w < n, σg.store.read p Su w = some (I.tape .uniform (n * d + w)) := by
    intro w hw
    rw [hgfr _ _ _ (Or.inl dSuSg), hurd w hw, h7p, hpos.1]
  have hSgR : ∀ w < 4 * (n * n), σg.store.read p Sg w =
      some (I.tape .gaussian (4 * (n * n) * d + w)) := by
    intro w hw
    rw [hgrd w hw, hupos]
    simp [h7p, hpos.2]
  have hrg : ∀ q b i, b < tH → b ≠ Su → b ≠ Sg →
      ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      σg.store.read q b i = st.store.read q b i := fun q b i hb h1 h2 h3 => by
    rw [hgfr _ _ _ (Or.inl h2), hufr _ _ _ (Or.inl h1), h7s]
    exact hr7 q b i hb h3
  have hSut : Su = tH → 1 ≤ n → n ≤ 5 := by
    intro hS hn
    obtain ⟨len, hlen, hi⟩ := Store.exists_getElem?_shape_of_read_eq_some (hSuR (n - 1) (by omega))
    rw [hshg, hS, hshape5, Option.some.injEq, Prod.mk.injEq] at hlen
    omega
  have hSgt : Sg = tH → 1 ≤ n → 4 * (n * n) ≤ 5 := by
    intro hS hn
    have hn2 : 0 < 4 * (n * n) := by positivity
    obtain ⟨len, hlen, hi⟩ :=
      Store.exists_getElem?_shape_of_read_eq_some (hSgR (4 * (n * n) - 1) (by omega))
    rw [hshg, hS, hshape5, Option.some.injEq, Prod.mk.injEq] at hlen
    omega
  have hH0 : H.Shaped σg.store p n D :=
    el1_shaped_of_eq (fun b hb => by
      rw [hshg, hS0, Store.getElem?_shape_push_of_lt _ (by
        simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)]) hH
  have htb : tH ∉ H.handles ++ [par, c] := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    omega
  have hnd' : H.handles.Nodup := hnd
  -- nodes of depth d: bounds and uniqueness
  have hbnd : ∀ {a : List Bool} {lo : ℕ} {y : EighNode K},
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) → 1 ≤ y.k →
        1 ≤ n ∧ lo + y.k ≤ n := by
    intro a lo y hl hk
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      cases a with
      | nil =>
        simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨-, rfl⟩ := hl
        exact absurd hk (by simp [hn])
      | cons b a =>
        have h0 : n ≤ 1 := by omega
        simp [eighLoc, eighStep, h0] at hl
    · exact ⟨hn, (eighLoc_bounds hn hl).2⟩
  have huniq : ∀ {a a' : List Bool} {lo : ℕ} {y y' : EighNode K}, a.length = d →
      a'.length = d → eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) →
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo, y') → 1 ≤ n → y = y' := by
    intro a a' lo y y' ha ha' hl hl' hn
    by_cases hae : a = a'
    · subst hae
      rw [hl] at hl'
      simp only [Option.some.injEq, Prod.mk.injEq] at hl'
      exact hl'.2
    · have h1 := (eighLoc_bounds hn hl).1
      have h2 := (eighLoc_bounds hn hl').1
      rcases eighLoc_disjoint (ha.trans ha'.symm) hae hl hl' with h | h <;> omega
  have hlp := el2_lp (mmR := mmR) (qrR := qrR) hsem p hu (fun p k hk => hlit p k (by omega))
    (R₀ := R₀) (ε := ε) hℓ d
  -- the loop over the slots
  have hex := exists_exec_loop_eq_some_of_forall I (n := .const n)
    (body := fun lo => (el1_slotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz
      H.Kd H.Kp c tH lo).run) (st := σg) (fun w (s : St P K C) =>
      s.store.shape = σg.store.shape ∧ s.pos = σg.pos ∧
      (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
        el1_done H I.sem s.store p M n F d R₀ β lo y) ∧
      ∀ q b i, (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
          ¬ el1_win H n d lo y.k (el1_childSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ
            (eighTapeSample n d lo)) lo) b i) → ¬ (b = tH ∧ i = 4) →
        s.store.read q b i = σg.store.read q b i)
    ⟨rfl, rfl, fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl⟩ ?_
  swap
  · rintro w hw s₁ ⟨hsh1, hps1, hdn1, hfr1⟩
    change w < n at hw
    have hn1 : 1 ≤ n := by omega
    have hrd1 : ∀ q b i, b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] → ¬ (b = tH ∧ i = 4) →
        s₁.store.read q b i = σg.store.read q b i :=
      fun q b i hb ht => hfr1 q b i (fun _ _ _ _ => el1_not_win_buf hb) ht
    have hSz1 : ∀ i, i < n * (d + 1) → s₁.store.read p H.Sz i = st.store.read p H.Sz i :=
      fun i hi => (hfr1 _ _ _ (fun _ _ _ _ => el1_not_win_Sz hnd' hi) (fun h => by omega)).trans
        (hrg _ _ _ lSz dSzSu dSzSg fun h => dSzLv h.1)
    have he4 : (n * (d + 1)) = n * d + n := by ring
    by_cases hnode : ∃ (y : EighNode K) (a : List Bool), a.length = d ∧
        eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y)
    · obtain ⟨y, a, ha, hl⟩ := hnode
      obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn1 hl
      obtain ⟨hyR, hyε, hyℓ⟩ := eighLoc_params hl
      rw [ha] at hyR hyε hyℓ
      have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
      have e5 : 2 * n * w + 2 * (n * y.k) ≤ 2 * (n * n) := by
        have := Nat.mul_le_mul_left (2 * n) hkn
        nlinarith
      have e6 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
      have ish : H.Shaped s₁.store p n D := el1_shaped_of_eq (fun b _ => by rw [hsh1]) hH0
      have iSz := el1_readsIdx_congr (hSz1 _ (by omega)) (hlev1 a w y ha hl).1
      have iA : pairLayout.Holds s₁.store p H.Ma (2 * (n * n) * d + 2 * n * w) y.A :=
        el1_holds_keep (hlev1 a w y ha hl).2 fun i h1 h2 =>
          (hfr1 _ _ _ (fun _ _ _ _ => el1_not_win_Ma hnd' (by omega)) (fun h => by omega)).trans
            (hrg _ _ _ lMa dMaSu dMaSg fun h => dMaLv h.1)
      have iR : s₁.store.read p H.Lv (2 * d) = some y.R := by
        rw [hrd1 p H.Lv (2 * d) hLvb (fun h => by omega),
          hrg p H.Lv (2 * d) lLv dLvSu dLvSg (fun h => by omega)]
        exact hlev3.trans (congrArg some hyR.symm)
      have iε : s₁.store.read p H.Lv (2 * d + 1) = some y.ε := by
        rw [hrd1 p H.Lv (2 * d + 1) hLvb (fun h => by omega),
          hrg p H.Lv (2 * d + 1) lLv dLvSu dLvSg (fun h => by omega)]
        exact hlev4.trans (congrArg some hyε.symm)
      have ipar : s₁.store.read p par 0 = some R₀ ∧ s₁.store.read p par 2 = some β :=
        ⟨by rw [hrd1 p par 0 hpb (fun h => by omega),
              hrg p par 0 lpar dparSu dparSg (fun h => dparLv h.1), hpar.1],
          by rw [hrd1 p par 2 hpb (fun h => by omega),
              hrg p par 2 lpar dparSu dparSg (fun h => dparLv h.1), hpar.2]⟩
      have iSu : 2 ≤ y.k → s₁.store.read p Su w = some (I.tape .uniform (n * d + w)) ∧
          (Su = tH → w ≠ 4) := fun hk2 => by
        have hSu4 : Su = tH → w ≠ 4 := fun hS => by have := hSut hS hn1; omega
        exact ⟨(hrd1 _ _ _ hSub fun h => hSu4 h.1 h.2).trans (hSuR w hw), hSu4⟩
      have iSg : 2 ≤ y.k → (∀ w' < 4 * (n * n), s₁.store.read p Sg w' =
          some (I.tape .gaussian (4 * (n * n) * d + w'))) ∧ Sg ≠ tH := fun hk2 => by
        have hSgT : Sg ≠ tH := fun hS => by
          have := hSgt hS hn1
          have : 2 ≤ n := by omega
          nlinarith
        exact ⟨fun w' hw' => (hrd1 _ _ _ hSgb fun h => hSgT h.1).trans (hSgR w' hw'), hSgT⟩
      have ic : s₁.store.read p c 0 = I.sem.lit p 1 ∧
          s₁.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
          s₁.store.read p c 2 = some (M.div M.one (M.ofNat 2)) ∧
          s₁.store.read p c 3 = some (M.neg M.one) ∧
          s₁.store.read p c 4 = some (I.sem.sqrtHalf p) :=
        ⟨by rw [hrd1 p c 0 hcb (fun h => by omega),
              hrg p c 0 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.1],
          by rw [hrd1 p c 1 hcb (fun h => by omega),
              hrg p c 1 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.1],
          by rw [hrd1 p c 2 hcb (fun h => by omega),
              hrg p c 2 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.1],
          by rw [hrd1 p c 3 hcb (fun h => by omega),
              hrg p c 3 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.2.1],
          by rw [hrd1 p c 4 hcb (fun h => by omega),
              hrg p c 4 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.2.2]⟩
      obtain ⟨s₂, hex⟩ := el2_slot_node_ex hmm hqr hsem p hu n ℓ₀ F d D hd (by omega) hlit htn H
        (par := par) (Su := Su) (Sg := Sg) (c := c) (t := tH) (s := s₁) (R₀ := R₀) (β := β)
        hk1 hkn ish hbufs htb ⟨5, by rw [hsh1, hshg]; exact hshape5, by norm_num⟩ iSz iA iR hR₀
        (fun h => by rw [hyR]; exact (hlp.1 h)) (fun h => by rw [hyR]; exact (hlp.2 h)) iε ipar
        (fun hk2 => ⟨⟨_, (iSu hk2).1⟩, (iSu hk2).2⟩)
        (fun hk2 => ⟨fun w' hw' => ⟨_, (iSg hk2).1 w' hw'⟩, (iSg hk2).2⟩)
        ⟨ic.1, ic.2.1, ⟨_, ic.2.2.1⟩, ⟨_, ic.2.2.2.1⟩, ic.2.2.2.2⟩
      obtain ⟨hdone, hfrW, hsh2, hps2⟩ := el1_slot_node hmm hqr p hflag hcmp n ℓ₀ F d D hd hlit htn
        H
        (par := par) (Su := Su) (Sg := Sg) (c := c) (t := tH) (s := s₁) (s' := s₂) (R₀ := R₀)
        (β := β) hk1 hkn hyℓ ish hbufs htb iSz iA iR iε ipar iSu iSg ic hex
      refine ⟨s₂, hex, hsh2.trans hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
        fun q b i hall ht4 => ?_⟩
      · obtain ⟨a', ha', hl'⟩ := hn'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
        · have hk1' := (eighLoc_bounds hn1 hl').1
          have hkn' := (eighLoc_bounds hn1 hl').2
          have hdis : lo + y'.k ≤ w := by
            have hae : a' ≠ a := fun h => by
              subst h
              rw [hl] at hl'
              have := (Prod.mk.inj (Option.some_inj.mp hl')).1
              omega
            rcases eighLoc_disjoint (ha'.trans ha.symm) hae hl' hl with h | h <;> omega
          exact el1_done_congr hk1' hkn' (fun b i hwin => hfrW p b i
            (fun hw' => el1_win_disjoint hnd' hk1' hdis hwin hw')
            (fun h => by have := hwinb hwin; omega)) (hdn1 lo y' hlo ⟨a', ha', hl'⟩)
        · rw [← huniq ha ha' hl hl' hn1]
          exact hdone
      · rw [hfrW q b i (hall w y (Nat.lt_succ_self w) ⟨a, ha, hl⟩) ht4]
        exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4
    · have hSz0 := hlev2 w hw (fun a y ha hl => hnode ⟨y, a, ha, hl⟩)
      have iSz0 := el1_readsIdx_congr (s' := s₁.store) (hSz1 _ (by omega)) hSz0
      obtain ⟨s₂, hex⟩ := el2_slot_skip_ex (mm := mm) (qr := qr) (n := n) (ℓ₀ := ℓ₀) (F := F)
        (d := d) (par := par) (Lv := H.Lv) (Su := Su) (Sg := Sg) (Ma := H.Ma) (Ua := H.Ua)
        (Qa := H.Qa) (Ea := H.Ea) (Kd := H.Kd) (Kp := H.Kp) (c := c) (t := tH) iSz0
      obtain ⟨hst, hps2⟩ := el1_slot_skip (s := s₁) (s' := s₂) iSz0 hex
      refine ⟨s₂, hex, by rw [hst]; exact hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
        fun q b i hall ht4 => ?_⟩
      · rw [hst]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
        · exact hdn1 lo y' hlo hn'
        · obtain ⟨a', ha', hl'⟩ := hn'
          exact absurd ⟨y', a', ha', hl'⟩ hnode
      · rw [hst]
        exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4
  obtain ⟨σe, he, -⟩ := hex
  exact el2_ex_seq he ⟨σe, exec_skip I σe⟩

end NLAlib
