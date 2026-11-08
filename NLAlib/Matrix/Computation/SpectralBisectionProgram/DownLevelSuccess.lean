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

omit [Inhabited K] in
/-- An allocation succeeds when its body does from the state with the fresh buffer pushed. -/
theorem exists_exec_alloc_of_exists {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st : St P K C}
    (h : ∃ st₂, exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st₂) :
    ∃ st', exec I (.alloc p len body) st = some st' := by
  obtain ⟨a, ha⟩ := h
  exact ⟨_, by rw [exec_alloc, ha]; rfl⟩

omit [Inhabited K] in
/-- A sequence succeeds when its first part does and the rest succeeds from there. -/
private theorem exists_exec_seq_of_left {a b : Stmt P ι ℕ ℕ} {s s₁ : St P K C}
    (h₁ : exec I a s = some s₁)
    (h₂ : ∃ st', exec I b s₁ = some st') : ∃ st', exec I (.seq a b) s = some st' := by
  obtain ⟨t, ht⟩ := h₂
  exact ⟨t, by rw [exec_seq, h₁, Option.bind_some, ht]⟩

omit [Inhabited K] in
/-- A goal on a state, for a named state equal to it. -/
theorem exists_exec_of_forall_eq {X : Stmt P ι ℕ ℕ} {s : St P K C}
    (h : ∀ σ : St P K C, σ = s → ∃ st', exec I X σ = some st') : ∃ st', exec I X s = some st' :=
  h s rfl

omit [Inhabited K] in
/-- An index literal, then the rest. -/
theorem exists_exec_seq_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {v : K} {s' : Store P K} (hv : I.sem.lit p (e.eval : ℚ) = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some st') :
    ∃ st', exec I (.seq (.instr (.litIdx p dst e)) t) s = some st' := by
  rw [exec_seq_instr_litIdx I hv hw]
  exact h

omit [Inhabited K] in
/-- A binary operation, then the rest. -/
theorem exists_exec_seq_bin {p : P} {b : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {a c v : K} {s' : Store P K} (hx : s.store.read p x.buf x.idx.eval = some a)
    (hy : s.store.read p y.buf y.idx.eval = some c) (hv : I.sem.bin p b a c = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p b) } = some st') :
    ∃ st', exec I (.seq (.instr (.bin p b dst x y)) t) s = some st' := by
  rw [exec_seq_instr_bin I hx hy hv hw]
  exact h

omit [Inhabited K] in
/-- A scoped index binder on a stored size within its bound. -/
private theorem exists_exec_bindIdx_seq_skip {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} {k : ℕ}
    (hr : ReadsIdx I.sem st.store p x.buf x.idx.eval k) (hk : k ≤ bound.eval)
    (h : ∃ st', exec I (body k) { st with cnt := st.cnt + I.charge (.toNat p) } = some st') :
    ∃ st', exec I (.seq (.bindIdx p x bound body) .skip) st = some st' := by
  unfold ReadsIdx at hr
  obtain ⟨w, hw, hv⟩ := Option.bind_eq_some_iff.mp hr
  rw [exec_seq_skip, exec_bindIdx_of_read I hw hv hk]
  exact h

omit [Inhabited K] in
/-- A loop of one iteration, then nothing. -/
private theorem exec_seq_loop_one_skip {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s : St P K C}
    (he : e.eval = 1) : exec I (.seq (.loop e b) .skip) s = exec I (b 0) s := by
  rw [exec_seq_skip, exec_loop, he]
  simp [List.range_one]

omit [Inhabited K] in
/-- A loop of no iteration, then nothing. -/
private theorem exec_seq_loop_zero_skip {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s : St P K C}
    (he : e.eval = 0) : exec I (.seq (.loop e b) .skip) s = some s := by
  rw [exec_seq_skip, exec_loop, he]
  rfl

omit [Inhabited K] in
/-- A loop of one iteration that succeeds. -/
private theorem exists_exec_seq_loop_one_skip {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s : St P K C}
    (he : e.eval = 1) (h : ∃ st', exec I (b 0) s = some st') :
    ∃ st', exec I (.seq (.loop e b) .skip) s = some st' := by
  rw [exec_seq_loop_one_skip he]
  exact h

omit [Inhabited K] in
/-- A guarded block, then the rest. -/
private theorem exists_exec_eighWhen_bind {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {s σ : St P K C}
    (h₁ : exec I (eighWhen e b).run s = some σ) (h₂ : ∃ st', exec I (f ()).run σ = some st') :
    ∃ st', exec I (eighWhen e b >>= f).run s = some st' := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl), h₁, Option.bind_some]
  exact h₂

omit [Inhabited K] in
/-- A conditional on a comparison of stored cells, then nothing. -/
private theorem exists_exec_seq_ite_skip {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {t e : Stmt P ι ℕ ℕ}
    {st : St P K C} {a b : K} {r : Bool} (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some b) (hc : I.sem.cmp p c a b = some r)
    (h : ∃ st', (if r then exec I t { st with cnt := st.cnt + I.charge (.cmp p) }
      else exec I e { st with cnt := st.cnt + I.charge (.cmp p) }) = some st') :
    ∃ st', exec I (.seq (.ite p c x y t e) .skip) st = some st' := by
  rw [exec_seq_skip, exec_ite]
  simp only [cmpStep, hx, hy, hc, Option.bind_some, Option.map_some]
  exact h

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- An arithmetic operation of the standard model succeeds, with its rounding. -/
theorem exists_bin_eq_some {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) {b : BinOp} (hb : b.IsArith)
    {x y : K} (hy : b = .div → dec p y ≠ 0) :
    ∃ z, I.sem.bin p b x y = some z ∧
      ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = b.realOp (dec p x) (dec p y) * (1 + δ) := by
  obtain ⟨z, hz⟩ := hsem.bin_ok p b x y hb hy trivial
  exact ⟨z, hz, hsem.bin_err p b x y z hb hz⟩

omit [Inhabited K] in
/-- A literal into a cell of a buffer, then nothing, succeeds and keeps the other buffers. -/
private theorem exists_exec_seq_lit_skip {p : P} {Y len : ℕ} {i : IExp ℕ} {q₀ : ℚ} {s : St P K C}
    (hz : ∃ z, I.sem.lit p q₀ = some z) (hY : s.store.shape[Y]? = some (p, len))
    (hi : i.eval < len) :
    ∃ s', exec I (.seq (.instr (.lit p ⟨Y, i⟩ q₀)) .skip) s = some s' ∧
      s'.store.shape = s.store.shape ∧
        ∀ q b j, b ≠ Y → s'.store.read q b j = s.store.read q b j := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s', hw⟩ := Store.exists_write_eq_some_of_getElem?_shape z hY hi
  refine ⟨_, (exec_seq_instr_lit I hz hw).trans (exec_skip I _), Store.shape_of_write_eq_some hw,
    fun q b j hb => Store.read_of_write_eq_some_of_ne hw (Or.inl hb)⟩

omit [Inhabited K] in
/-- A copy into a cell of a buffer, then nothing, succeeds and keeps the other buffers. -/
private theorem exists_exec_seq_copy_skip {p : P} {Y len : ℕ} {i : IExp ℕ} {src : Cell ℕ ℕ}
    {s : St P K C}
    (hx : ∃ v, s.store.read p src.buf src.idx.eval = some v)
    (hY : s.store.shape[Y]? = some (p, len)) (hi : i.eval < len) :
    ∃ s', exec I (.seq (.instr (.copy p ⟨Y, i⟩ src)) .skip) s = some s' ∧
      s'.store.shape = s.store.shape ∧
        ∀ q b j, b ≠ Y → s'.store.read q b j = s.store.read q b j := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨s', hw⟩ := Store.exists_write_eq_some_of_getElem?_shape v hY hi
  refine ⟨_, (exec_seq_instr_copy I hv hw).trans (exec_skip I _), Store.shape_of_write_eq_some hw,
    fun q b j hb => Store.read_of_write_eq_some_of_ne hw (Or.inl hb)⟩

omit [Inhabited K] in
/-- A loop whose steps succeed, keeping the shape and the buffers other than `Y`. -/
private theorem exists_exec_loop_of_frame {m : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {Y : ℕ}
    {st : St P K C}
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

omit [Inhabited K] in
/-- A leaf succeeds when its blocks are allocated and its matrix is stored. -/
private theorem exists_exec_eighLeafBlock {u : P → ℝ} {dec : P → K → ℝ}
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
  obtain ⟨s1, h1, sh1, fr1⟩ := exists_exec_loop_of_frame (Y := Ua) (st := st)
    (m := 2 * (IExp.const k * IExp.const k))
    (body := fun w => .seq (.instr (.lit p ⟨Ua, uo + .var w⟩ 0)) .skip)
    (fun w hw s hs _ => exists_exec_seq_lit_skip hz0 (by rw [hs]; exact hUa) (by
      change uo.eval + w < lU
      change w < 2 * (k * k) at hw
      omega))
  obtain ⟨s2, h2, sh2, fr2⟩ := exists_exec_loop_of_frame (Y := Ua) (st := s1) (m := IExp.const k)
    (body := fun i => .seq (.instr (.lit p ⟨Ua, uo + zidx (.const k) (.var i) (.var i)⟩ 1)) .skip)
    (fun i hi s hs _ => exists_exec_seq_lit_skip hz1 (by rw [hs, sh1]; exact hUa) (by
      change uo.eval + 2 * (i + k * i) < lU
      change i < k at hi
      have := hii i hi
      omega))
  have hMa2 : ∀ i < k, ∃ v, s2.store.read p Ma (mo.eval + 2 * (i + k * i)) = some v := by
    intro i hi
    rw [fr2 _ _ _ hMaUa, fr1 _ _ _ hMaUa]
    exact ⟨_, hA ⟨i, hi⟩ ⟨i, hi⟩ ⟨0, two_pos⟩⟩
  obtain ⟨s3, h3, sh3, fr3⟩ := exists_exec_loop_of_frame (Y := Ea) (st := s2) (m := IExp.const k)
    (body := fun i => ((if diag then Builder.ins (ι := ι) (.copy p ⟨Ea, eo + .var i⟩
        ⟨Ma, mo + zidx (.const k) (.var i) (.var i)⟩)
      else Builder.ins (.lit p ⟨Ea, eo + .var i⟩ 0)) : Builder P ι ℕ ℕ Unit).run)
    (fun i hi s hs hf => by
      change i < k at hi
      cases diag
      · exact exists_exec_seq_lit_skip hz0 (by rw [hs, sh2, sh1]; exact hEa)
          (by change eo.eval + i < lE; omega)
      · refine exists_exec_seq_copy_skip ?_ (by rw [hs, sh2, sh1]; exact hEa) (by
          change eo.eval + i < lE; omega)
        obtain ⟨v, hv⟩ := hMa2 i hi
        exact ⟨v, (hf _ _ _ hMaEa).trans hv⟩)
  obtain ⟨s4, hw4⟩ := Store.exists_write_eq_some_of_getElem?_shape z1'
    (by rw [sh3, sh2, sh1]; exact hKd) hK
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) .skip)))
    (.seq (.loop _ _) (.seq (.instr (.litIdx p kd 1)) .skip))) st = some st'
  refine exists_exec_seq_of_left (s₁ := s2) ?_ (exists_exec_seq_of_left h3
    ⟨_, (exec_seq_instr_litIdx I (v := z1') hz1' hw4).trans (exec_skip I _)⟩)
  rw [exec_named]
  exact (exec_seq_of_exec_eq_some I h1).trans ((exec_seq_of_exec_eq_some I h2).trans
    (exec_skip I _))

omit [DecidableEq P] [AddMonoid C] in
/-- The windows of the levels decode to positive values from a positive $R_0$ and to $0$
from a zero $R_0$. -/
private theorem eighLevelParams_fst_pos_zero {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (hlit : IsExactIntLit dec I.sem 2) {R₀ ε : K} {ℓ₀ : ℕ} (hℓ : 1 ≤ ℓ₀) :
    ∀ d, (0 < dec p R₀ → 0 < dec p (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1) ∧
      (dec p R₀ = 0 → dec p (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1 = 0) := by
  classical
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
    obtain ⟨h1, hh1, δ1, hδ1, hd1⟩ := exists_bin_eq_some hsem p (b := .div) trivial (x := one) (y :=
        two)
      (fun _ => by rw [htwo']; norm_num)
    obtain ⟨h2, hh2, δ2, hδ2, hd2⟩ := exists_bin_eq_some hsem p (b := .div) trivial (x := two) (y :=
        L)
      (fun _ => ne_of_gt hLpos)
    obtain ⟨h3, hh3, δ3, hδ3, hd3⟩ := exists_bin_eq_some hsem p (b := .add) trivial (x := h1) (y :=
        h2)
      (fun h => by cases h)
    obtain ⟨h4, hh4, δ4, hδ4, hd4⟩ := exists_bin_eq_some hsem p (b := .mul) trivial (x := h3)
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

omit [Inhabited K] in
/-- A slot of `NLAlib.eighDownLevel` whose size cell reads $0$ succeeds. -/
private theorem exists_exec_slotBody_of_zero {p : P} {mm qr : ι}
    {n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo : ℕ} {s : St P K C}
    (hSz : ReadsIdx I.sem s.store p Sz (n * d + lo) 0) :
    ∃ s', exec I (eighSlotBody p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo).run s =
      some s' := by
  unfold eighSlotBody
  refine exists_exec_bindIdx_seq_skip (k := 0) (by exact hSz) (Nat.zero_le _) ?_
  exact ⟨_, exec_seq_loop_zero_skip (by change 1 - (1 - 0) = 0; omega)⟩

omit [Inhabited K] in
/-- Under the standard model, the leaf block of the slot `lo` of depth $d < D$ succeeds from a
store whose arenas are allocated and hold the matrix of the node $y$ ($1 \le k$,
$lo + k \le n$) at its offset. -/
private theorem exists_exec_slotBody_leaf {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (diag : Bool) {n d D : ℕ}
    (hd : d < D) {H : EighArenas} {lo : ℕ} {y : EighNode K} (hk1 : 1 ≤ y.k) (hkn : lo + y.k ≤ n)
    {σ : St P K C} (hH : H.Shaped σ.store p n D)
    (hA : pairLayout.Holds σ.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A) :
    ∃ σ', exec I (eighLeafBlock (ι := ι) p diag (.var y.k) H.Ma
      (eighBlockOff (.const n) (.const d) (.var lo)) H.Ua
      (eighBlockOff (.const n) (.const d) (.var lo)) H.Ea
      (eighSlotOff (.const n) (.const d) (.var lo))
      ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩).run σ = some σ' := by
  obtain ⟨hnd, -, hUa, -, hEa, -, hKd, -, -⟩ := hH
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
  obtain ⟨σ', h'⟩ := exists_exec_eighLeafBlock hsem p diag y.k (A := y.A) (st := σ) (Ma := H.Ma)
    (Ua := H.Ua) (Ea := H.Ea) (mo := eighBlockOff (.const n) (.const d) (.var lo))
    (uo := eighBlockOff (.const n) (.const d) (.var lo))
    (eo := eighSlotOff (.const n) (.const d) (.var lo))
    (kd := ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) (by exact hA) hUa
    (by change 2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ _; omega)
    hEa (by change n * d + lo + y.k ≤ _; omega) hKd (by change n * d + lo < _; omega)
    (fun h => by simp [EighArenas.handles, h] at hnd)
    (fun h => by simp [EighArenas.handles, h] at hnd)
  exact ⟨σ', (exec_eighLeafBlock_var p diag y.k H.Ma H.Ua H.Ea _ _ _ _ _).trans h'⟩

/-- Under the standard model with $u(p) < 1$, exact integer literals up to $n + 4$, the exact
floor conversion and kernels that are routines on pairs, the slot `lo` of a node $y$ of depth
$d < D$ ($1 \le k$, $lo + k \le n$, $\ell_0 + d \ge 1$) succeeds from a store whose arenas are
allocated and hold its size, matrix, window and tolerance, with $R_0 \ge 0$ in `par[0]`, $\beta$
in `par[2]`, the samples (for $k \ge 2$), the constants in `c` and the scratch buffer `t` (outside
the arenas, `par` and `c`, of length above $4$): a window $R$ is positive when $R_0$ is and $0$
when $R_0$ is, so a node step's window is positive once its window test fails. -/
private theorem exists_exec_slotBody_node {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
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
    ∃ s', exec I (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c t lo).run s = some s' := by
  have dtLv : H.Lv ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtMa : H.Ma ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtpar : par ≠ t := fun h => ht (by simp [h])
  have dtc : c ≠ t := fun h => ht (by simp [h])
  unfold eighSlotBody
  refine exists_exec_bindIdx_seq_skip (k := y.k) (by exact hSz) (by change y.k ≤ n - lo; omega) ?_
  refine exists_exec_seq_loop_one_skip (by change 1 - (1 - y.k) = 1; omega) ?_
  rcases Nat.lt_or_ge y.k 2 with hk | hk
  · obtain ⟨σ', h'⟩ := exists_exec_slotBody_leaf
      (σ := { s with cnt := s.cnt + I.charge (.toNat p) }) hsem p true hd hk1 hkn hH hA
    refine exists_exec_eighWhen_bind (σ := σ') ?_ ?_
    · exact (exec_seq_loop_one_skip (e := 1 - (1 - (1 - (IExp.var y.k - 1))))
        (by change 1 - (1 - (1 - (y.k - 1))) = 1; omega)).trans h'
    · exact ⟨_, exec_seq_loop_zero_skip (by change 1 - (1 - (y.k - 1)) = 0; omega)⟩
  refine exists_exec_eighWhen_bind
    (exec_seq_loop_zero_skip (by change 1 - (1 - (1 - (y.k - 1))) = 0; omega)) ?_
  refine exists_exec_seq_loop_one_skip (by change 1 - (1 - (y.k - 1)) = 1; omega) ?_
  obtain ⟨len, htsh, hlen⟩ := ht4
  obtain ⟨v, hv, δ, hδ, hvd⟩ := exists_bin_eq_some hsem p (b := .mul) trivial (x := y.ε) (y := R₀)
    (fun h => by cases h)
  obtain ⟨s₂, hw2⟩ := Store.exists_write_eq_some_of_getElem?_shape v htsh hlen
  have hr2 : ∀ q b i, b ≠ t → s₂.read q b i = s.store.read q b i :=
    fun q b i hne => Store.read_of_write_eq_some_of_ne hw2 (Or.inl hne)
  have hH2 : H.Shaped s₂ p n D :=
    EighArenas.Shaped.of_shape_eq (fun b _ => by rw [Store.shape_of_write_eq_some hw2]) hH
  have hA2 : pairLayout.Holds s₂ p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A :=
    pairLayout_holds_of_read_eq hA fun i _ _ => hr2 _ _ _ dtMa
  refine exists_exec_seq_bin (s' := s₂) (by exact hε) (by exact hpar.1) hv (by exact hw2) ?_
  change ∃ st', exec I (.seq (.ite _ _ _ _ _ _) .skip) _ = some st'
  refine exists_exec_seq_ite_skip (a := y.R) (b := v) (by exact (hr2 _ _ _ dtLv).trans hR)
    (by exact Store.read_of_write_eq_some hw2) (hsem.cmp_le p y.R v) ?_
  by_cases hle : dec p y.R ≤ dec p v
  · rw [if_pos (decide_eq_true hle)]
    exact exists_exec_slotBody_leaf hsem p false hd hk1 hkn (by exact hH2) hA2
  rw [if_neg (by simpa using hle)]
  have hRp : 0 < dec p y.R := by
    refine hR₀.lt_or_eq.elim hRpos fun h => absurd ?_ hle
    rw [hRz h.symm, hvd, ← h]
    simp [BinOp.realOp]
  obtain ⟨⟨w, hSu1⟩, hSu2⟩ := hSu hk
  obtain ⟨hSg1, hSg2⟩ := hSg hk
  have hcv : ∀ {i v}, s.store.read p c i = v → s₂.read p c i = v := fun h => (hr2 _ _ _ dtc).trans h
  obtain ⟨sN, hN⟩ := exists_exec_eighNodeBlock hmm hqr hsem
    (fun p k hk => hlit p k (by omega)) htn p hu n ℓ₀ F d lo y.k
    (fun p k hk => hlit p k (by omega)) hkn hk hℓ H (A := y.A)
    (R := y.R) (β := β) (st := { s with store := s₂, cnt := _ }) hd hH2 hbufs hA2
    ((hr2 _ _ _ dtLv).trans hR) hRp ((hr2 _ _ _ dtpar).trans hpar.2)
    ⟨w, (Store.read_of_write_eq_some_of_ne hw2 (by tauto)).trans hSu1⟩
    (fun w hw => (hSg1 w hw).imp fun _ hx => (hr2 _ _ _ hSg2).trans hx)
    ⟨hcv hc.1, hcv hc.2.1, hc.2.2.1.imp fun _ => hcv, hc.2.2.2.1.imp fun _ => hcv,
      hcv hc.2.2.2.2⟩
  exact ⟨sN, (exec_eighNodeBlock_var p mm qr n ℓ₀ F d lo y.k par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp
      c
    _).trans hN⟩

/-- A buffer outside the arenas is none of the seven arenas a slot writes. -/
private theorem not_mem_winArenas {H : EighArenas} {b : ℕ} (hb : b ∉ H.handles) :
    b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := fun h => hb (by
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  omega)

/-- The window arena `Lv` is none of the seven arenas a slot writes. -/
private theorem lv_not_mem_winArenas {H : EighArenas} (hnd : H.handles.Nodup) :
    H.Lv ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
  intro h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hnd

omit [Inhabited K] in
/-- Two nodes that `NLAlib.eighLoc` reaches at one slot by paths of one length from a root of
size $n \ge 1$ are equal. -/
private theorem eq_of_eighLoc_eq_some {M : FloatMachine K ℕ ℕ} {n F ℓ₀ : ℕ} {R₀ ε β : K}
    {A : Matrix (Fin n) (Fin n) (K × K)} {a a' : List Bool} {lo : ℕ} {y y' : EighNode K}
    (hn : 1 ≤ n) (ha : a.length = a'.length)
    (hl : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (hl' : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo, y')) : y = y' := by
  by_cases hae : a = a'
  · subst hae
    rw [hl, Option.some.injEq, Prod.mk.injEq] at hl'
    exact hl'.2
  · have h1 := (eighLoc_bounds hn hl).1
    have h2 := (eighLoc_bounds hn hl').1
    rcases eighLoc_disjoint ha hae hl hl' with h | h <;> omega

/-- The invariant of the loop over the slots of `NLAlib.eighDownLevel` after the slots below `w`,
from the state `σ`: the shape and tape positions of `σ`, the slots below `w` of the nodes of depth
$d$ are done (`NLAlib.EighSlotDone`), and every cell outside their windows and the scratch cell
`t[4]`
reads as in `σ`. -/
private def DownSlotsInv (I : Interp P ι K C) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K))
    (p : P) (n F ℓ₀ d : ℕ) (H : EighArenas) (A : Matrix (Fin n) (Fin n) (K × K)) (R₀ ε β : K)
    (t : ℕ) (σ : St P K C) (w : ℕ) (s : St P K C) : Prop :=
  s.store.shape = σ.store.shape ∧ s.pos = σ.pos ∧
    (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
      EighSlotDone H I.sem s.store p (eighTapeMachine I p mmR qrR) n F d R₀ β lo y) ∧
    ∀ q b i, (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
        ¬ EighSlotWindow H n d lo y.k (EighChildSlot (eighStep (eighTapeMachine I p mmR qrR) n F R₀
            β
          y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i) → ¬ (b = t ∧ i = 4) →
      s.store.read q b i = σ.store.read q b i

/-- One slot of a node in the loop of `NLAlib.eighDownLevel`: under the standard model with
$u(p) < 1$, exact integer literals up to $n + 4$, the exact floor conversion, kernels that are
routines on pairs, $\ell_0 \ge 1$ and $R_0 \ge 0$, from the state `σ` after the parameters and
draws of the level (the arenas allocated and holding the nodes of depth $d < D$, $R_0$ and $\beta$
in `par`, the constants in `c`, the samples of the level in `Su`, `Sg`, a scratch buffer `t` of
length $5$ outside the arenas, `par` and `c`), the slot `w < n` of a node $y$ of depth $d$
succeeds from a state of the loop invariant `DownSlotsInv` after `w` slots and keeps it after
`w + 1`. -/
private theorem exists_exec_slotBody_inv_node {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (hu : u p < 1) (n ℓ₀ F d D : ℕ) (hd : d < D) (hℓ : 1 ≤ ℓ₀)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c t : ℕ} {σ s : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hR₀ : 0 ≤ dec p R₀) (hH : H.Shaped σ.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (ht : t ∉ H.handles ++ [par, c])
    (ht5 : σ.store.shape[t]? = some (p, 5))
    (hlev : H.LevelHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : σ.store.read p par 0 = some R₀ ∧ σ.store.read p par 2 = some β)
    (hc : σ.store.read p c 0 = I.sem.lit p 1 ∧ σ.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      σ.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      σ.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      σ.store.read p c 4 = some (I.sem.sqrtHalf p))
    (hSu : ∀ w < n, σ.store.read p Su w = some (I.tape .uniform (n * d + w)))
    (hSg : ∀ w < 4 * (n * n), σ.store.read p Sg w =
      some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hSut : Su = t → n ≤ 5) (hSgt : Sg = t → n ≤ 1) {w : ℕ} (hw : w < n) {a : List Bool}
    {y : EighNode K} (ha : a.length = d)
    (hl : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y))
    (hs : DownSlotsInv I mmR qrR p n F ℓ₀ d H A R₀ ε β t σ w s) :
    ∃ s', exec I (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c t w).run s = some s' ∧
        DownSlotsInv I mmR qrR p n F ℓ₀ d H A R₀ ε β t σ (w + 1) s' := by
  obtain ⟨hsh1, hps1, hdn1, hfr1⟩ := hs
  have hnd := hH.1
  have hn1 : 1 ≤ n := by omega
  have dt : ∀ {b}, b ∈ H.handles ++ [par, c] → b ≠ t := fun hb h => ht (h ▸ hb)
  have hout : ∀ {x}, x ∈ [par, Su, Sg, c] → x ∉ H.handles :=
    fun hx hm => List.disjoint_of_nodup_append hbufs hm hx
  have hrd : ∀ q b i, b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] → ¬ (b = t ∧ i = 4) →
      s.store.read q b i = σ.store.read q b i :=
    fun q b i hb ht' => hfr1 q b i (fun _ _ _ _ => not_eighSlotWindow_of_not_mem hb) ht'
  have hLv := lv_not_mem_winArenas hnd
  have dLv : H.Lv ≠ t := dt (by simp [EighArenas.handles])
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn1 hl
  obtain ⟨hyR, hyε, hyℓ⟩ := eighLoc_params hl
  rw [ha] at hyR hyε hyℓ
  have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
  have e5 : 2 * n * w + 2 * (n * y.k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) hkn
    nlinarith
  have e6 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have he4 : n * (d + 1) = n * d + n := by ring
  have iSz := readsIdx_of_read_eq (hfr1 _ _ _ (fun _ _ _ _ => not_eighSlotWindow_sz hnd (by omega))
    fun h => dt (by simp [EighArenas.handles]) h.1) (hlev.1 a w y ha hl).1
  have iA : pairLayout.Holds s.store p H.Ma (2 * (n * n) * d + 2 * n * w) y.A :=
    pairLayout_holds_of_read_eq (hlev.1 a w y ha hl).2 fun i h1 h2 => hfr1 _ _ _
      (fun _ _ _ _ => not_eighSlotWindow_ma hnd (by omega)) fun h => dt (by simp
          [EighArenas.handles]) h.1
  have iR := (hrd p _ _ hLv fun h => dLv h.1).trans (hlev.2.2.1.trans (congrArg some hyR.symm))
  have iε := (hrd p _ _ hLv fun h => dLv h.1).trans (hlev.2.2.2.trans (congrArg some hyε.symm))
  have hkw : ∀ {x i v}, x ∈ [par, c] → σ.store.read p x i = v → s.store.read p x i = v :=
    fun {x i _} hx h => (hrd p x i (not_mem_winArenas (hout (by simp at hx ⊢; tauto))) fun h' =>
      dt (List.mem_append_right _ hx) h'.1).trans h
  have hpw : ∀ {i v}, σ.store.read p par i = v → s.store.read p par i = v := hkw (by simp)
  have hcw : ∀ {i v}, σ.store.read p c i = v → s.store.read p c i = v := hkw (by simp)
  have iSu : 2 ≤ y.k → s.store.read p Su w = some (I.tape .uniform (n * d + w)) ∧
      (Su = t → w ≠ 4) := fun hk2 =>
    have hSu4 : Su = t → w ≠ 4 := fun hS => by have := hSut hS; omega
    ⟨(hrd p Su w (not_mem_winArenas (hout (by simp))) fun h => hSu4 h.1 h.2).trans (hSu w hw),
      hSu4⟩
  have iSg : 2 ≤ y.k → (∀ w' < 4 * (n * n), s.store.read p Sg w' =
      some (I.tape .gaussian (4 * (n * n) * d + w'))) ∧ Sg ≠ t := fun hk2 =>
    have hSgT : Sg ≠ t := fun hS => by have := hSgt hS; omega
    ⟨fun w' hw' => (hrd p Sg w' (not_mem_winArenas (hout (by simp))) fun h =>
      hSgT h.1).trans (hSg w' hw'), hSgT⟩
  have hlp := eighLevelParams_fst_pos_zero (mmR := mmR) (qrR := qrR) hsem p hu
    (fun p k hk => hlit p k (by omega)) (R₀ := R₀) (ε := ε) hℓ d
  have ish : H.Shaped s.store p n D := EighArenas.Shaped.of_shape_eq (fun b _ => by rw [hsh1]) hH
  obtain ⟨s₂, hex⟩ := exists_exec_slotBody_node hmm hqr hsem p hu n ℓ₀ F d D hd (by omega) hlit
    htn H (t := t) (R₀ := R₀) (β := β) hk1 hkn ish hbufs ht
    ⟨5, by rw [hsh1]; exact ht5, by norm_num⟩ iSz iA iR hR₀ (fun h => by rw [hyR]; exact hlp.1 h)
    (fun h => by rw [hyR]; exact hlp.2 h) iε ⟨hpw hpar.1, hpw hpar.2⟩
    (fun hk2 => ⟨⟨_, (iSu hk2).1⟩, (iSu hk2).2⟩)
    (fun hk2 => ⟨fun w' hw' => ⟨_, (iSg hk2).1 w' hw'⟩, (iSg hk2).2⟩)
    ⟨hcw hc.1, hcw hc.2.1, ⟨_, hcw hc.2.2.1⟩, ⟨_, hcw hc.2.2.2.1⟩, hcw hc.2.2.2.2⟩
  obtain ⟨hdone, hfrW, hsh2, hps2⟩ := holds_of_exec_eighSlotBody hmm hqr p
      (hsem.decidesFlags (fun q k hk => hlit q k (hk.trans (by omega))) p)
    (hsem.cmp_le p) n ℓ₀ F d D hlit htn H (t := t) (s' := s₂) (R₀ := R₀) (β := β) hk1 hkn hyℓ
    ish hbufs ht iSz iA iR iε ⟨hpw hpar.1, hpw hpar.2⟩ iSu iSg
    ⟨hcw hc.1, hcw hc.2.1, hcw hc.2.2.1, hcw hc.2.2.2.1, hcw hc.2.2.2.2⟩ hex
  refine ⟨s₂, hex, hsh2.trans hsh1, hps2.trans hps1, fun lo y' hlo ⟨a', ha', hl'⟩ => ?_,
    fun q b i hall ht4 => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
    · obtain ⟨hk1', hkn'⟩ := eighLoc_bounds hn1 hl'
      have hdis : lo + y'.k ≤ w := by
        have hae : a' ≠ a := fun h => by
          subst h
          rw [hl] at hl'
          have := (Prod.mk.inj (Option.some_inj.mp hl')).1
          omega
        rcases eighLoc_disjoint (ha'.trans ha.symm) hae hl' hl with h | h <;> omega
      exact EighSlotDone.of_read_eq hk1' hkn' (fun b i hwin => hfrW p b i
        (fun hw' => false_of_eighSlotWindow_of_eighSlotWindow hnd hk1' hdis hwin hw') fun h => dt
            (List.mem_append_left _
          (Classical.byContradiction fun hb => not_mem_winArenas hb (mem_of_eighSlotWindow hwin)))
              h.1)
        (hdn1 lo y' hlo ⟨a', ha', hl'⟩)
    · rw [← eq_of_eighLoc_eq_some hn1 (ha.trans ha'.symm) hl hl']
      exact hdone
  · rw [hfrW q b i (hall w y (Nat.lt_succ_self w) ⟨a, ha, hl⟩) ht4]
    exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4

/-- The loop over the slots of `NLAlib.eighDownLevel` succeeds: under the standard model with
$u(p) < 1$, exact integer literals up to $n + 4$, the exact floor conversion, kernels that are
routines on pairs, $\ell_0 \ge 1$ and $R_0 \ge 0$, from a state `σ` whose arenas are allocated
and hold the nodes of depth $d < D$, with $R_0$ and $\beta$ in `par`, the constants in `c`, the
samples of the level in `Su`, `Sg` and a scratch buffer `t` of length $5$ outside the arenas,
`par` and `c`. -/
private theorem exists_exec_eighDownLevel_slots {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (hu : u p < 1) (n ℓ₀ F d D : ℕ) (hd : d < D) (hℓ : 1 ≤ ℓ₀)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c t : ℕ} {σ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hR₀ : 0 ≤ dec p R₀) (hH : H.Shaped σ.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (ht : t ∉ H.handles ++ [par, c])
    (ht5 : σ.store.shape[t]? = some (p, 5))
    (hlev : H.LevelHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : σ.store.read p par 0 = some R₀ ∧ σ.store.read p par 2 = some β)
    (hc : σ.store.read p c 0 = I.sem.lit p 1 ∧ σ.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      σ.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      σ.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      σ.store.read p c 4 = some (I.sem.sqrtHalf p))
    (hSu : ∀ w < n, σ.store.read p Su w = some (I.tape .uniform (n * d + w)))
    (hSg : ∀ w < 4 * (n * n), σ.store.read p Sg w =
      some (I.tape .gaussian (4 * (n * n) * d + w))) :
    ∃ σ', exec I (.loop (.const n) fun lo => (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma
      H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo).run) σ = some σ' := by
  have hex := exists_exec_loop_eq_some_of_forall I (n := .const n) (st := σ)
    (body := fun lo => (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c t lo).run) (DownSlotsInv I mmR qrR p n F ℓ₀ d H A R₀ ε β t σ)
    ⟨rfl, rfl, fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl⟩ ?_
  · exact hex.imp fun _ h => h.1
  intro w hw s hs
  change w < n at hw
  by_cases hnode : ∃ (y : EighNode K) (a : List Bool), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y)
  · obtain ⟨y, a, ha, hl⟩ := hnode
    refine exists_exec_slotBody_inv_node hmm hqr hsem p hu n ℓ₀ F d D hd hℓ hlit htn H hR₀ hH
      hbufs ht ht5 hlev hpar hc hSu hSg (fun hS => ?_) (fun hS => ?_) hw ha hl hs
    · obtain ⟨len, hlen, hi⟩ := Store.exists_getElem?_shape_of_read_eq_some (hSu (n - 1) (by omega))
      rw [hS, ht5, Option.some.injEq, Prod.mk.injEq] at hlen
      omega
    · obtain ⟨len, hlen, hi⟩ := Store.exists_getElem?_shape_of_read_eq_some
        (hSg (4 * (n * n) - 1)
          (by have := Nat.mul_le_mul (show 1 ≤ n by omega) (show 1 ≤ n by omega); omega))
      rw [hS, ht5, Option.some.injEq, Prod.mk.injEq] at hlen
      by_contra h2
      have : 4 ≤ n * n := Nat.mul_le_mul (by omega : 2 ≤ n) (by omega : 2 ≤ n)
      omega
  obtain ⟨hsh1, hps1, hdn1, hfr1⟩ := hs
  have he4 : n * (d + 1) = n * d + n := by ring
  have iSz0 := readsIdx_of_read_eq (s' := s.store)
    (hfr1 _ _ _ (fun _ _ _ _ => not_eighSlotWindow_sz hH.1 (by omega))
      fun h => ht (h.1 ▸ by simp [EighArenas.handles]))
    (hlev.2.1 w hw fun a y ha hl => hnode ⟨y, a, ha, hl⟩)
  obtain ⟨s₂, hex⟩ := exists_exec_slotBody_of_zero (mm := mm) (qr := qr) (n := n) (ℓ₀ := ℓ₀)
    (F := F) (d := d) (par := par) (Lv := H.Lv) (Su := Su) (Sg := Sg) (Ma := H.Ma) (Ua := H.Ua)
    (Qa := H.Qa) (Ea := H.Ea) (Kd := H.Kd) (Kp := H.Kp) (c := c) (t := t) iSz0
  obtain ⟨hst, hps2⟩ := store_eq_of_exec_eighSlotBody iSz0 hex
  refine ⟨s₂, hex, hst ▸ hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
    fun q b i hall ht4 => hst ▸ hfr1 q b i
      (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4⟩
  rw [hst]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
  · exact hdn1 lo y' hlo hn'
  · obtain ⟨a', ha', hl'⟩ := hn'
    exact absurd ⟨y', a', ha', hl'⟩ hnode

omit [Inhabited K] in
/-- The draws of `NLAlib.eighDownLevel` ($n$ uniform into `Su`, $4n^2$ Gaussian into `Sg`, two
distinct buffers long enough) succeed, and so does what follows when it succeeds from every state
of the same shape that reads as `σ` outside `Su` and `Sg` and holds the tape values from the
positions of `σ` there. -/
private theorem exists_exec_eighDownLevel_draws (p : P) {n Su Sg : ℕ} {X : Stmt P ι ℕ ℕ}
    {σ : St P K C} (hSuSg : Su ≠ Sg)
    (hSu : ∃ len, σ.store.shape[Su]? = some (p, len) ∧ n ≤ len)
    (hSg : ∃ len, σ.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len)
    (hX : ∀ σ' : St P K C, σ'.store.shape = σ.store.shape →
      (∀ q b i, b ≠ Su → b ≠ Sg → σ'.store.read q b i = σ.store.read q b i) →
      (∀ w < n, σ'.store.read p Su w = some (I.tape .uniform (σ.pos .uniform + w))) →
      (∀ w < 4 * (n * n), σ'.store.read p Sg w = some (I.tape .gaussian (σ.pos .gaussian + w))) →
      ∃ st', exec I X σ' = some st') :
    ∃ st', exec I (.seq (.loop (.const n) fun i =>
        (Builder.ins (ι := ι) (.draw p .uniform ⟨Su, .var i⟩)).run)
      (.seq (.loop (4 * (IExp.const n * IExp.const n)) fun w =>
        (Builder.ins (ι := ι) (.draw p .gaussian ⟨Sg, .var w⟩)).run) X)) σ = some st' := by
  obtain ⟨len1, hSush, hlen1⟩ := hSu
  obtain ⟨len2, hSgsh, hlen2⟩ := hSg
  obtain ⟨σu, hdu, hur, hufr, hush, hupos, -⟩ := exec_forRange_draw I p .uniform Su 0 (.const n)
    (fun i => .var i) (fun i => (Nat.zero_add i).symm) σ (fun i hi =>
      ⟨_, Store.exists_write_eq_some_of_getElem?_shape (I.tape .uniform 0) hSush
        (by change i < n at hi; omega)⟩)
  obtain ⟨σg, hdg, hgr, hgfr, hgsh, -⟩ := exec_forRange_draw I p .gaussian Sg 0
    (4 * (IExp.const n * IExp.const n)) (fun w => .var w) (fun w => (Nat.zero_add w).symm) σu
    (fun w hw => ⟨_, Store.exists_write_eq_some_of_getElem?_shape (I.tape .gaussian 0)
      (by rw [hush]; exact hSgsh) (by change w < 4 * (n * n) at hw; omega)⟩)
  refine exists_exec_seq_of_left ((exec_seq_skip I _ _).symm.trans hdu)
    (exists_exec_seq_of_left ((exec_seq_skip I _ _).symm.trans hdg) (hX σg (hgsh.trans hush)
      (fun q b i h1 h2 => (hgfr q b i fun h => absurd h h2).trans (hufr q b i fun h => absurd h h1))
      (fun w hw => ?_) fun w hw => ?_))
  · rw [hgfr _ _ _ fun h => absurd h hSuSg]
    simpa using hur w hw
  · simpa [hupos] using hgr w hw

omit [Inhabited K] in
/-- Under the standard model with $u(p) < 1$ and exact literals up to $2$: from a state with a
scratch buffer `t` of length $5$ and the window arena `Lv` of length $2(D + 1)$ (distinct from
each other and from `c`), with $\mathrm{fl}(2)$ in `c[1]`, values in `c[2]` and `Lv[2d]`, and
$\ell_0 + d \ge 1$, the first four instructions of `NLAlib.eighDownLevel` (the counter
$\ell_0 + d$ into `t[0]`, then `t[2]`, `t[3]` and the next window into `Lv[2(d + 1)]`) succeed,
and so does what follows when it succeeds from every state of the same shape and tape positions
that reads as `σ` outside `t` and `Lv[2(d + 1)]` and holds a positive counter in `t[0]`. -/
private theorem exists_exec_eighDownLevel_window {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) {ℓ₀ d D t Lv c : ℕ}
    (hℓ : 1 ≤ ℓ₀ + d) (hd : d < D) {X : Stmt P ι ℕ ℕ} {σ : St P K C} {tw hf R : K}
    (ht5 : σ.store.shape[t]? = some (p, 5)) (hLv : σ.store.shape[Lv]? = some (p, 2 * (D + 1)))
    (dLv : Lv ≠ t) (dc : c ≠ t) (h1 : σ.store.read p c 1 = some tw)
    (h2 : σ.store.read p c 2 = some hf) (hR : σ.store.read p Lv (2 * d) = some R)
    (hX : ∀ σ' : St P K C, σ'.store.shape = σ.store.shape → σ'.pos = σ.pos →
      (∀ q b i, b ≠ t → ¬ (b = Lv ∧ i = 2 * (d + 1)) → σ'.store.read q b i = σ.store.read q b i) →
      (∃ v, σ'.store.read p t 0 = some v ∧ 0 < dec p v) → ∃ st', exec I X σ' = some st') :
    ∃ st', exec I (.seq (.instr (.litIdx p ⟨t, 0⟩ (.const ℓ₀ + .const d)))
      (.seq (.instr (.bin p .div ⟨t, 2⟩ ⟨c, 1⟩ ⟨t, 0⟩))
      (.seq (.instr (.bin p .add ⟨t, 3⟩ ⟨c, 2⟩ ⟨t, 2⟩))
      (.seq (.instr (.bin p .mul ⟨Lv, 2 * (.const d + 1)⟩ ⟨t, 3⟩ ⟨Lv, 2 * .const d⟩)) X)))) σ =
        some st' := by
  obtain ⟨v0, hv0⟩ := hsem.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) trivial
  have hv0pos : 0 < dec p v0 := by
    obtain ⟨δ, hδ, hvd⟩ := hsem.lit_err p _ v0 hv0
    rw [hvd]
    have hx : (0 : ℝ) < (((ℓ₀ + d : ℕ) : ℚ) : ℝ) := by exact_mod_cast (show 0 < ℓ₀ + d by omega)
    exact mul_pos hx (by linarith [(abs_le.mp hδ).1])
  obtain ⟨v1, hv1, -⟩ := exists_bin_eq_some hsem p (b := .div) trivial (x := tw) (y := v0)
    (fun _ => ne_of_gt hv0pos)
  obtain ⟨v2, hv2, -⟩ := exists_bin_eq_some hsem p (b := .add) trivial (x := hf) (y := v1)
    (fun h => by cases h)
  obtain ⟨v3, hv3, -⟩ := exists_bin_eq_some hsem p (b := .mul) trivial (x := v2) (y := R) (fun h =>
      by cases h)
  obtain ⟨S1, hw0⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) v0 ht5 (by norm_num)
  have sh1 := Store.shape_of_write_eq_some hw0
  obtain ⟨S2, hw1⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2) v1
    (by rw [sh1]; exact ht5) (by norm_num)
  have sh2 := Store.shape_of_write_eq_some hw1
  obtain ⟨S3, hw2⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 3) v2
    (by rw [sh2, sh1]; exact ht5) (by norm_num)
  have sh3 := Store.shape_of_write_eq_some hw2
  obtain ⟨S4, hw3⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2 * (d + 1)) v3
    (by rw [sh3, sh2, sh1]; exact hLv) (by omega)
  have hfr : ∀ q b i, b ≠ t → ¬ (b = Lv ∧ i = 2 * (d + 1)) → S4.read q b i = σ.store.read q b i :=
    fun q b i hb hL => by
      rw [Store.read_of_write_eq_some_of_ne hw3 (by tauto), Store.read_of_write_eq_some_of_ne hw2
        (Or.inl hb), Store.read_of_write_eq_some_of_ne hw1 (Or.inl hb),
        Store.read_of_write_eq_some_of_ne hw0 (Or.inl hb)]
  refine exists_exec_seq_litIdx (by exact hv0) (by exact hw0) ?_
  refine exists_exec_seq_bin (by exact (Store.read_of_write_eq_some_of_ne hw0 (Or.inl dc)).trans h1)
    (by exact Store.read_of_write_eq_some hw0) hv1 (by exact hw1) ?_
  have r2 : S2.read p c 2 = some hf := (Store.read_of_write_eq_some_of_ne hw1 (Or.inl dc)).trans
    ((Store.read_of_write_eq_some_of_ne hw0 (Or.inl dc)).trans h2)
  have r3 : S3.read p Lv (2 * d) = some R :=
    (Store.read_of_write_eq_some_of_ne hw2 (Or.inl dLv)).trans
      ((Store.read_of_write_eq_some_of_ne hw1 (Or.inl dLv)).trans
        ((Store.read_of_write_eq_some_of_ne hw0 (Or.inl dLv)).trans hR))
  refine exists_exec_seq_bin (by exact r2) (by exact Store.read_of_write_eq_some hw1) hv2 (by exact
      hw2) ?_
  refine exists_exec_seq_bin (by exact Store.read_of_write_eq_some hw2) (by exact r3) hv3 (by exact
      hw3) ?_
  refine hX _ ((Store.shape_of_write_eq_some hw3).trans (sh3.trans (sh2.trans sh1))) rfl hfr
    ⟨v0, ?_, hv0pos⟩
  change S4.read p t 0 = _
  rw [Store.read_of_write_eq_some_of_ne hw3 (Or.inl dLv.symm),
    Store.read_of_write_eq_some_of_ne hw2 (Or.inr (by omega)),
    Store.read_of_write_eq_some_of_ne hw1 (Or.inr (by omega)), Store.read_of_write_eq_some hw0]

omit [Inhabited K] in
/-- Under the standard model: from a state with a scratch buffer `t` of length $5$ and the window
arena `Lv` of length $2(D + 1)$ (distinct from each other and from `c`), with values in `c[0]` and
`Lv[2d + 1]` and a positive counter in `t[0]`, the next three instructions of
`NLAlib.eighDownLevel` (`t[1]`, `t[3]` and the next tolerance into `Lv[2(d + 1) + 1]`) succeed,
and so does what follows when it succeeds from every state of the same shape and tape positions
that reads as `σ` outside `t` and `Lv[2(d + 1) + 1]`. -/
private theorem exists_exec_eighDownLevel_tol {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) {d D t Lv c : ℕ} (hd : d < D)
    {X : Stmt P ι ℕ ℕ} {σ : St P K C} {o v0 E : K}
    (ht5 : σ.store.shape[t]? = some (p, 5)) (hLv : σ.store.shape[Lv]? = some (p, 2 * (D + 1)))
    (dLv : Lv ≠ t) (dc : c ≠ t) (h0 : σ.store.read p c 0 = some o)
    (ht0 : σ.store.read p t 0 = some v0) (hv0 : 0 < dec p v0)
    (hE : σ.store.read p Lv (2 * d + 1) = some E)
    (hX : ∀ σ' : St P K C, σ'.store.shape = σ.store.shape → σ'.pos = σ.pos →
      (∀ q b i, b ≠ t → ¬ (b = Lv ∧ i = 2 * (d + 1) + 1) →
        σ'.store.read q b i = σ.store.read q b i) → ∃ st', exec I X σ' = some st') :
    ∃ st', exec I (.seq (.instr (.bin p .div ⟨t, 1⟩ ⟨c, 0⟩ ⟨t, 0⟩))
      (.seq (.instr (.bin p .sub ⟨t, 3⟩ ⟨c, 0⟩ ⟨t, 1⟩))
      (.seq (.instr (.bin p .mul ⟨Lv, 2 * (.const d + 1) + 1⟩ ⟨t, 3⟩ ⟨Lv, 2 * .const d + 1⟩))
        X))) σ = some st' := by
  obtain ⟨v4, hv4, -⟩ := exists_bin_eq_some hsem p (b := .div) trivial (x := o) (y := v0)
    (fun _ => ne_of_gt hv0)
  obtain ⟨v5, hv5, -⟩ := exists_bin_eq_some hsem p (b := .sub) trivial (x := o) (y := v4) (fun h =>
      by cases h)
  obtain ⟨v6, hv6, -⟩ := exists_bin_eq_some hsem p (b := .mul) trivial (x := v5) (y := E) (fun h =>
      by cases h)
  obtain ⟨S5, hw4⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) v4 ht5 (by norm_num)
  have sh5 := Store.shape_of_write_eq_some hw4
  obtain ⟨S6, hw5⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 3) v5
    (by rw [sh5]; exact ht5) (by norm_num)
  have sh6 := Store.shape_of_write_eq_some hw5
  obtain ⟨S7, hw6⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2 * (d + 1) + 1) v6
    (by rw [sh6, sh5]; exact hLv) (by omega)
  refine exists_exec_seq_bin (by exact h0) (by exact ht0) hv4 (by exact hw4) ?_
  refine exists_exec_seq_bin (by exact (Store.read_of_write_eq_some_of_ne hw4 (Or.inl dc)).trans h0)
    (by exact Store.read_of_write_eq_some hw4) hv5 (by exact hw5) ?_
  have r6 : S6.read p Lv (2 * d + 1) = some E :=
    (Store.read_of_write_eq_some_of_ne hw5 (Or.inl dLv)).trans
      ((Store.read_of_write_eq_some_of_ne hw4 (Or.inl dLv)).trans hE)
  refine exists_exec_seq_bin (by exact Store.read_of_write_eq_some hw5) (by exact r6) hv6 (by exact
      hw6) ?_
  refine hX _ ((Store.shape_of_write_eq_some hw6).trans (sh6.trans sh5)) rfl fun q b i hb hL => ?_
  change S7.read q b i = _
  rw [Store.read_of_write_eq_some_of_ne hw6 (by tauto), Store.read_of_write_eq_some_of_ne hw5
    (Or.inl hb), Store.read_of_write_eq_some_of_ne hw4 (Or.inl hb)]

omit [AddMonoid C] [Inhabited K] in
/-- The nodes of depth $d$ transfer to a store that reads the same at `p` on the size and node
arenas and on the window and tolerance cells below $2d + 2$. -/
private theorem levelHolds_of_read_eq {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K}
    {p : P} {M : FloatMachine K ℕ ℕ} {n F ℓ₀ d : ℕ} {R₀ β : K} {root : EighNode K}
    (hs : ∀ b i, (b = H.Ma ∨ b = H.Sz ∨ (b = H.Lv ∧ i < 2 * d + 2)) →
      s'.read p b i = s.read p b i)
    (h : H.LevelHolds sem s p M n F ℓ₀ R₀ β root d) :
    H.LevelHolds sem s' p M n F ℓ₀ R₀ β root d := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun a lo y ha hl => ?_, fun lo hlo hno =>
    readsIdx_of_read_eq (hs _ _ (Or.inr (Or.inl rfl))) (h2 lo hlo hno),
    (hs _ _ (Or.inr (Or.inr ⟨rfl, by omega⟩))).trans h3,
    (hs _ _ (Or.inr (Or.inr ⟨rfl, by omega⟩))).trans h4⟩
  obtain ⟨r1, r2⟩ := h1 a lo y ha hl
  exact ⟨readsIdx_of_read_eq (hs _ _ (Or.inr (Or.inl rfl))) r1,
    pairLayout_holds_of_read_eq r2 fun i _ _ => hs _ _ (Or.inl rfl)⟩

/-- One level of the downward pass succeeds: under the standard model at $u$ with every value in
range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor conversion, kernels
that are routines on pairs `mmR`, `qrR`, $\ell_0 \ge 1$, $\varepsilon$ and $R_0$ decoding to
nonnegative values, and $M$ = `NLAlib.eighTapeMachine I p mmR qrR` with the root
$(n, \mathbf{A}, R_0, \varepsilon, \ell_0)$: a run of `NLAlib.eighDownLevel` at depth $d < D$ from
a state whose arenas are allocated and hold the nodes of depth $d$
(`NLAlib.EighArenas.LevelHolds`), with $R_0$, $\beta$ in `par`, sample buffers `Su`, `Sg` of
lengths at least $n$ and $4n^2$, the tape positions $nd$ (uniform) and $4n^2 d$ (Gaussian), and the
constants in `c` (cells $0$ to $4$: one, $\mathrm{fl}(2)$, $\mathrm{fl}(1/2)$, $-1$, the stored
$\sqrt{1/2}$), succeeds. No printed source. -/
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
    ∃ st', exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv
      Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
        some st' := by
  have _ := hε
  set tH := st.store.size with htH
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < tH :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  obtain ⟨-, o1, -, hl1, -, -⟩ := hsem.decidesFlags (fun q k hk => hlit q k (hk.trans (by omega))) p
  obtain ⟨tw, htw, -⟩ := hlit p 2 (by omega)
  have lpar := Store.lt_size_of_read_eq_some hpar.1
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans hl1)
  have lLv := hsz hLv
  obtain ⟨len1, hSush, hlen1⟩ := hSu
  obtain ⟨len2, hSgsh, hlen2⟩ := hSg
  have harena : ∀ b ∈ H.handles, b < tH := fun b hb => by
    simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSzs, hsz hKd, hsz hKp, lLv]
  have hout : ∀ {b x}, b ∈ H.handles → x ∈ [par, Su, Sg, c] → b ≠ x :=
    fun hb hx h => List.disjoint_of_nodup_append hbufs hb (by rw [h]; exact hx)
  have hLvm : H.Lv ∈ H.handles := by simp [EighArenas.handles]
  have dLvc : H.Lv ≠ c := hout hLvm (by simp)
  have dparSu : par ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSg : par ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSu : c ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSg : c ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSuSg : Su ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  change ∃ st', exec I (.seq (.alloc p _ _) .skip) st = some st'
  rw [exec_seq_skip]
  refine exists_exec_alloc_of_exists (exists_exec_of_forall_eq fun σ0 hσ0 => ?_)
  have hS0 : ∀ q b i, b < tH → σ0.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [hσ0]; exact Store.read_push_of_lt hb
  have hsh0 : ∀ {b}, b < tH → σ0.store.shape[b]? = st.store.shape[b]? := fun hb => by
    rw [hσ0]; exact Store.getElem?_shape_push_of_lt _ hb
  have ht5 : σ0.store.shape[tH]? = some (p, 5) := by
    rw [hσ0]; exact Store.getElem?_shape_push_size _ _ _
  have hps0 : σ0.pos = st.pos := by rw [hσ0]
  have hLv0 := (hsh0 lLv).trans hLv
  refine exists_exec_eighDownLevel_window (σ := σ0) (t := tH) (Lv := H.Lv) (c := c) hsem p hu
    (by omega) hd ht5 hLv0 (by omega) (by omega) ((hS0 _ _ _ lc).trans (hc.2.1.trans htw))
    ((hS0 _ _ _ lc).trans hc.2.2.1) ((hS0 _ _ _ lLv).trans hlev.2.2.1)
    fun σ1 hsh1 hps1 hfr1 ⟨v0, hv0, hv0p⟩ => ?_
  refine exists_exec_eighDownLevel_tol (σ := σ1) hsem p hd (by rw [hsh1]; exact ht5)
    (by rw [hsh1]; exact hLv0) (by omega) (by omega)
    ((hfr1 _ _ _ (by omega) fun h => dLvc h.1.symm).trans ((hS0 _ _ _ lc).trans (hc.1.trans hl1)))
    hv0 hv0p ((hfr1 _ _ _ (by omega) fun h => by omega).trans ((hS0 _ _ _ lLv).trans hlev.2.2.2))
    fun σ7 hsh7 hps7 hfr7 => ?_
  have hsh := hsh7.trans hsh1
  refine exists_exec_eighDownLevel_draws p dSuSg
    ⟨len1, by rw [hsh, hsh0 (hsz hSush)]; exact hSush, hlen1⟩
    ⟨len2, by rw [hsh, hsh0 (hsz hSgsh)]; exact hSgsh, hlen2⟩ fun σg hshg hfrg hSuR hSgR => ?_
  have hfr : ∀ q b i, b < tH → b ≠ Su → b ≠ Sg → ¬ (b = H.Lv ∧ 2 * (d + 1) ≤ i) →
      σg.store.read q b i = st.store.read q b i := fun q b i hb h1 h2 h3 => by
    rw [hfrg q b i h1 h2, hfr7 q b i (by omega) (fun h => h3 ⟨h.1, by omega⟩),
      hfr1 q b i (by omega) (fun h => h3 ⟨h.1, by omega⟩), hS0 q b i hb]
  have hfrc : ∀ {i}, σg.store.read p c i = st.store.read p c i :=
    hfr _ _ _ lc dcSu dcSg fun h => dLvc h.1.symm
  have hfrp : ∀ {i}, σg.store.read p par i = st.store.read p par i :=
    hfr _ _ _ lpar dparSu dparSg fun h => hout hLvm (by simp) h.1.symm
  have hlev' := levelHolds_of_read_eq (s' := σg.store) (fun b i hb => hfr _ _ _
    (harena _ (by rcases hb with rfl | rfl | ⟨rfl, -⟩ <;> simp [EighArenas.handles]))
    (hout (by rcases hb with rfl | rfl | ⟨rfl, -⟩ <;> simp [EighArenas.handles]) (by simp))
    (hout (by rcases hb with rfl | rfl | ⟨rfl, -⟩ <;> simp [EighArenas.handles]) (by simp))
    fun ⟨hL, hi⟩ => by
      rcases hb with rfl | rfl | ⟨-, hb⟩
      · simp [EighArenas.handles, hL] at hnd
      · simp [EighArenas.handles, hL] at hnd
      · omega) hlev
  obtain ⟨σe, he⟩ := exists_exec_eighDownLevel_slots hmm hqr hsem p hu n ℓ₀ F d D hd hℓ hlit htn H
    hR₀ (σ := σg) (t := tH) (EighArenas.Shaped.of_shape_eq (fun b hb => by
      rw [hshg, hsh, hsh0 (harena b hb)]) hH) hbufs
    (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => lt_irrefl _ (harena _ h), by omega, by omega⟩)
    (by rw [hshg, hsh]; exact ht5) hlev' ⟨hfrp.trans hpar.1, hfrp.trans hpar.2⟩
    ⟨hfrc.trans hc.1, hfrc.trans hc.2.1, hfrc.trans hc.2.2.1, hfrc.trans hc.2.2.2.1,
      hfrc.trans hc.2.2.2.2⟩
    (fun w hw => by rw [hSuR w hw, hps7, hps1, hps0, hpos.1])
    (fun w hw => by rw [hSgR w hw, hps7, hps1, hps0, hpos.2])
  exact exists_exec_seq_of_left he ⟨σe, exec_skip I σe⟩

end NLAlib
