/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PairKernels

/-!
# Complex-pair kernels: the Hermitian shift and scaling

The rounded specifications of the kernels `NLAlib.Computation.zhermShift` ($\mathbf{A} -
c\mathbf{I}$) and `NLAlib.Computation.zhermScale` ($\mathbf{A}/c$), which compute the upper triangle
of a Hermitian matrix and complete it by `NLAlib.Computation.zmirror`: a successful run writes the
machine's `hermShift` and `hermScale`, and the run succeeds when its operations do.

## Main results

* `NLAlib.Computation.holds_of_exec_zhermShift`, `NLAlib.Computation.holds_of_exec_zhermScale`: what
  a successful run computes.
* `NLAlib.Computation.exists_exec_zhermShift`, `NLAlib.Computation.exists_exec_zhermScale`: when the
  run succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The Hermitian kernels -/

/-- The invariant of the loops of the Hermitian kernels: the shape and the tape positions of
`st`, every cell outside the block at `Y` as in `st`, and both parts of every entry in `S`
written with the parts of $\mathbf{B}$. -/
def ZInv (p : P) (n Y yo : ℕ) (st : St P K C) (B : Fin n → Fin n → K × K)
    (S : Fin n → Fin n → Prop) (σ : St P K C) : Prop :=
  σ.store.shape = st.store.shape ∧ σ.pos = st.pos ∧
    (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, 2 * (n * n)) = true →
      σ.store.read q b i = st.store.read q b i) ∧
    ∀ a b : Fin n, S a b → σ.store.read p Y (yo + 2 * (a + n * b)) = some (B a b).1 ∧
      σ.store.read p Y (yo + 2 * (a + n * b) + 1) = some (B a b).2

omit [Inhabited K] [AddMonoid C] in
private theorem ZInv.mono {p : P} {n Y yo : ℕ} {st σ : St P K C} {B : Fin n → Fin n → K × K}
    {S S' : Fin n → Fin n → Prop} (h : ZInv p n Y yo st B S σ) (hS : ∀ a b, S' a b → S a b) :
    ZInv p n Y yo st B S' σ :=
  ⟨h.1, h.2.1, h.2.2.1, fun a b hab => h.2.2.2 a b (hS a b hab)⟩

theorem zherm_lt {n a b : ℕ} (ha : a < n) (hb : b < n) :
    2 * (a + n * b) + 1 < 2 * (n * n) := by
  nlinarith

omit [Inhabited K] in
/-- A write inside the block at `Y` keeps the cells outside it. -/
theorem zherm_write_frame {s s' s₀ : Store P K} {p : P} {Y yo N k : ℕ} {v : K}
    (hw : s.write p Y (yo + k) v = some s') (hk : k < N)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s.read q b i = s₀.read q b i) :
    ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = s₀.read q b i := by
  intro q b i hb
  refine (Store.read_of_write_eq_some_of_ne hw ?_).trans (hfr q b i hb)
  simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
  by_cases hbY : b = Y
  · exact Or.inr (by omega)
  · exact Or.inl hbY

omit [Inhabited K] [AddMonoid C] in
/-- The step of the invariant: writing both parts of the entry $(i_0, j_0)$ of
$\mathbf{B}$. -/
theorem ZInv.step {p : P} {n Y yo : ℕ} {st s σ : St P K C}
    {B : Fin n → Fin n → K × K} {S : Fin n → Fin n → Prop} (h : ZInv p n Y yo st B S s)
    (i₀ j₀ : Fin n) {s' s'' : Store P K}
    (hw1 : s.store.write p Y (yo + 2 * (i₀ + n * j₀)) (B i₀ j₀).1 = some s')
    (hw2 : s'.write p Y (yo + 2 * (i₀ + n * j₀) + 1) (B i₀ j₀).2 = some s'')
    (hσ : σ.store = s'') (hpos : σ.pos = s.pos) :
    ZInv p n Y yo st B (fun a b => S a b ∨ (a = i₀ ∧ b = j₀)) σ := by
  obtain ⟨sh, ps, fr, hS⟩ := h
  have hk := zherm_lt i₀.2 j₀.2
  subst hσ
  refine ⟨(Store.shape_of_write_eq_some hw2).trans ((Store.shape_of_write_eq_some hw1).trans sh),
    hpos.trans ps, zherm_write_frame (k := 2 * (i₀ + n * j₀) + 1) hw2 hk
      (zherm_write_frame (k := 2 * (i₀ + n * j₀)) hw1 (by omega) fr), fun a b hab => ?_⟩
  by_cases he : a = i₀ ∧ b = j₀
  · obtain ⟨rfl, rfl⟩ := he
    exact ⟨(Store.read_of_write_eq_some_of_ne hw2 (Or.inr (by omega))).trans
      (Store.read_of_write_eq_some hw1), Store.read_of_write_eq_some hw2⟩
  · have hab' : S a b := hab.resolve_right he
    have hne : a.1 + n * b.1 ≠ i₀.1 + n * j₀.1 := fun e => he
      (by have := zmirror_index_inj a.2 i₀.2 e; exact ⟨Fin.ext this.1, Fin.ext this.2⟩)
    obtain ⟨h1, h2⟩ := hS a b hab'
    exact ⟨(Store.read_of_write_eq_some_of_ne hw2 (Or.inr (by omega))).trans
        ((Store.read_of_write_eq_some_of_ne hw1 (Or.inr (by omega))).trans h1),
      (Store.read_of_write_eq_some_of_ne hw2 (Or.inr (by omega))).trans
        ((Store.read_of_write_eq_some_of_ne hw1 (Or.inr (by omega))).trans h2)⟩

omit [Inhabited K] in
private theorem zherm_inv_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ} {s s₂ : St P K C}
    (h : exec I (.seq (.instr (.copy p dst src)) t) s = some s₂) :
    ∃ v s', s.store.read p src.buf src.idx.eval = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.copy p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
theorem zherm_inv_bin {p : P} {op : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.bin p op dst x y)) t) s = some s₂) :
    ∃ a c v s', s.store.read p x.buf x.idx.eval = some a ∧
      s.store.read p y.buf y.idx.eval = some c ∧ I.sem.bin p op a c = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p op) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, c, hc, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, c, v, s', ha, hc, hv, hw, h⟩

omit [Inhabited K] in
theorem zherm_inv_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.lit p dst q)) t) s = some s₂) :
    ∃ v s', I.sem.lit p q = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] [AddMonoid C] in
/-- The parts of $\mathbf{A}$ survive in every store framed outside the block at `Y`. -/
theorem zherm_readX {p : P} {n X Y xo yo : ℕ} {st σ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo A)
    (hXY : blockDisjoint (Y, yo, 2 * (n * n)) (X, xo, 2 * (n * n)) = true)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, 2 * (n * n)) = true →
      σ.store.read q b i = st.store.read q b i) (a b : Fin n) :
    σ.store.read p X (xo + 2 * (a + n * b)) = some (A a b).1 ∧
      σ.store.read p X (xo + 2 * (a + n * b) + 1) = some (A a b).2 := by
  have hk := zherm_lt a.2 b.2
  have hd : ∀ k < 2 * (n * n), blockDisjoint (X, xo + k, 1) (Y, yo, 2 * (n * n)) = true := by
    intro k hk
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXY ⊢
    omega
  exact ⟨(hfr _ _ _ (hd _ (by omega))).trans (hA a b ⟨0, Nat.zero_lt_two⟩),
    (hfr _ _ _ (hd _ hk)).trans (hA a b ⟨1, Nat.one_lt_two⟩)⟩

omit [Inhabited K] in
/-- The two loops of a Hermitian kernel: if each step of the upper loop writes the entry
$(i, j)$, $i < j$, of $\mathbf{B}$ and each step of the diagonal loop the entry $(i, i)$, keeping
the invariant, the run ends the loops with the upper triangle and the diagonal of $\mathbf{B}$
written. -/
theorem zherm_loops {p : P} {n Y yo : ℕ} {st st' : St P K C}
    {B : Fin n → Fin n → K × K} {bodyU : ℕ → ℕ → Stmt P ι ℕ ℕ} {bodyD : ℕ → Stmt P ι ℕ ℕ}
    {rest : Stmt P ι ℕ ℕ}
    (hup : ∀ (i j : Fin n), i < j → ∀ S (s s₂ : St P K C), ZInv p n Y yo st B S s →
      exec I (bodyU j i) s = some s₂ → ZInv p n Y yo st B (fun a b => S a b ∨ (a = i ∧ b = j)) s₂)
    (hdg : ∀ (i : Fin n), ∀ S (s s₂ : St P K C), ZInv p n Y yo st B S s →
      exec I (bodyD i) s = some s₂ → ZInv p n Y yo st B (fun a b => S a b ∨ (a = i ∧ b = i)) s₂)
    (h : exec I (.seq (.loop (.const n) fun j => .seq (.loop (.var j) fun i => bodyU j i) .skip)
      (.seq (.loop (.const n) bodyD) rest)) st = some st') :
    ∃ σ, ZInv p n Y yo st B (fun a b => a ≤ b) σ ∧ exec I rest σ = some st' := by
  rw [exec_seq, Option.bind_eq_some_iff] at h
  obtain ⟨σ₁, h₁, h⟩ := h
  rw [exec_seq, Option.bind_eq_some_iff] at h
  obtain ⟨σ₂, h₂, h₃⟩ := h
  have hU := forall_of_exec_loop_eq_some I
    (fun j s => ZInv p n Y yo st B (fun a b => a < b ∧ b.1 < j) s)
    ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ b h => absurd h.2 (Nat.not_lt_zero _)⟩ (by
      intro j hj s₁ s₂ hR hex
      simp only [IExp.eval_const] at hj
      rw [exec_seq_skip] at hex
      refine (forall_of_exec_loop_eq_some I
        (fun i s => ZInv p n Y yo st B (fun a b => a < b ∧ (b.1 < j ∨ b.1 = j ∧ a.1 < i)) s)
        (hR.mono fun a b h => ⟨h.1, h.2.elim id fun h => absurd h.2 (Nat.not_lt_zero _)⟩)
        ?_ hex).mono fun a b h => ⟨h.1, by
          have : a.1 < b.1 := h.1
          have h2 := h.2
          simp only [IExp.eval_var]
          omega⟩
      · intro i hi s₁ s₂ hR hex
        simp only [IExp.eval_var] at hi
        have hab : (⟨i, by omega⟩ : Fin n) < ⟨j, hj⟩ := Fin.mk_lt_mk.mpr hi
        refine (hup ⟨i, by omega⟩ ⟨j, hj⟩ hab _ s₁ s₂ hR hex).mono fun a b h => ?_
        by_cases he : a.1 = i ∧ b.1 = j
        · exact Or.inr ⟨Fin.ext he.1, Fin.ext he.2⟩
        · have : a.1 < b.1 := h.1
          refine Or.inl ⟨h.1, ?_⟩
          omega) h₁
  have hD := forall_of_exec_loop_eq_some I
    (fun i s => ZInv p n Y yo st B (fun a b => a < b ∨ (a = b ∧ a.1 < i)) s)
    (hU.mono fun a b h => h.elim (fun h => ⟨h, b.2⟩) fun h => absurd h.2 (Nat.not_lt_zero _))
    (by
      intro i hi s₁ s₂ hR hex
      simp only [IExp.eval_const] at hi
      refine (hdg ⟨i, hi⟩ _ s₁ s₂ hR hex).mono fun a b h => ?_
      by_cases he : a.1 = i ∧ b.1 = i
      · exact Or.inr ⟨Fin.ext he.1, Fin.ext he.2⟩
      · refine Or.inl (h.imp id fun h => ⟨h.1, ?_⟩)
        have := congrArg Fin.val h.1
        omega) h₂
  refine ⟨σ₂, hD.mono fun a b h => ?_, h₃⟩
  rcases lt_or_eq_of_le h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, a.2⟩

/-- The mirror ends a Hermitian kernel. -/
theorem zherm_finish {p : P} {n Y : ℕ} {yo : IExp ℕ} {st σ st' : St P K C}
    {B : Fin n → Fin n → K × K} (h : ZInv p n Y yo.eval st B (fun a b => a ≤ b) σ)
    (hdiag : ∀ i, (B i i).2 = (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero)
    (h₃ : exec I (zmirror (ι := ι) p (.const n) Y yo).run σ = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermFrom (fun i j => B i j)
        fun i => (B i i).1) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  obtain ⟨sh, ps, fr, hS⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := holds_of_exec_zmirror (toNat := toNat) (mmR := mmR) (qrR := qrR)
    (unif := unif) (normal := normal) p n (B := B) hS hdiag h₃
  exact ⟨h1, fun q b i hb => (h2 q b i hb).trans (fr q b i hb), h3.trans sh, h4.trans ps⟩

omit [Inhabited K] in
theorem zherm_hermFrom_ite {Su Sg : Type} {n : ℕ} (M : FloatMachine K Su Sg)
    (up : Fin n → Fin n → K × K) (dg : Fin n → K) :
    M.hermFrom (fun i j => if i < j then up i j else (dg i, M.zero))
      (fun i => (if i < i then up i i else (dg i, M.zero)).1) = M.hermFrom up dg := by
  ext i j <;> simp only [FloatMachine.hermFrom, Matrix.of_apply, lt_irrefl, if_false] <;>
    split_ifs <;> rfl

/-- `zhermShift` computes the machine's shift: a successful run of
`NLAlib.Computation.zhermShift` from a state whose block at `X` holds the complex $n \times n$
matrix $\mathbf{A}$ and whose cell `c` holds $c$, into a block at `Y` disjoint from the block at
`X` and from `c`, ends with the block at `Y` holding `M.hermShift A c` for the machine `M` of the
semantics at `p`, every cell outside it unchanged, the same store shape and the same tape
positions. No printed source. -/
theorem holds_of_exec_zhermShift (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    (h : exec I (zhermShift (ι := ι) p (.const n) X xo c Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift A cv) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  have hprog : (zhermShift (ι := ι) p (.const n) X xo c Y yo).run = .seq (.named "zhermShift"
      [.idx (.const n), .buf X, .idx xo, .cell c, .buf Y, .idx yo]
      (.seq (.loop (.const n) fun j => .seq (.loop (.var j) fun i =>
        .seq (.instr (.copy p ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
          ⟨X, xo + zidx (.const n) (.var i) (.var j)⟩))
          (.seq (.instr (.copy p ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
            ⟨X, xo + zidx (.const n) (.var i) (.var j) + 1⟩)) .skip)) .skip)
      (.seq (.loop (.const n) fun i =>
        .seq (.instr (.bin p .sub ⟨Y, yo + zidx (.const n) (.var i) (.var i)⟩
          ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩ c))
          (.seq (.instr (.lit p ⟨Y, yo + zidx (.const n) (.var i) (.var i) + 1⟩ 0)) .skip))
        (zmirror (ι := ι) p (.const n) Y yo).run))) .skip := rfl
  rw [hprog, exec_seq_skip, exec_named] at h
  let B : Fin n → Fin n → K × K := fun i j =>
    if i < j then A i j else (M.sub (A i i).1 cv, M.zero)
  refine (fun hL => ?_) (zherm_loops (p := p) (Y := Y) (yo := yo.eval) (B := B)
    (fun i j hij S s s₂ hR hex => ?_)
    (fun i S s s₂ hR hex => ?_) h)
  · obtain ⟨σ, hσ, h₃⟩ := hL
    have hfin := zherm_finish (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
      (normal := normal) hσ (fun i => by simp only [B, lt_irrefl, if_false]; rfl) h₃
    rwa [show M.hermShift A cv = M.hermFrom (fun i j => B i j) (fun i => (B i i).1) from
      (zherm_hermFrom_ite M _ _).symm]
  · obtain ⟨v1, s', hr1, hw1, hex⟩ := zherm_inv_copy hex
    obtain ⟨v2, s'', hr2, hw2, hex⟩ := zherm_inv_copy hex
    rw [exec_skip, Option.some_inj] at hex
    subst hex
    have fr := hR.2.2.1
    simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
      IExp.eval_ofNat] at hr1 hw1 hr2 hw2
    rw [(zherm_readX hA hXY fr i j).1, Option.some_inj] at hr1
    subst hr1
    have fr' := zherm_write_frame (k := 2 * (i + n * j)) hw1
      (by have := zherm_lt i.2 j.2; omega) fr
    rw [(zherm_readX hA hXY (σ := { s with store := s' }) fr' i j).2, Option.some_inj] at hr2
    subst hr2
    have hB : B i j = A i j := if_pos hij
    exact ZInv.step hR i j (by rw [hB]; exact hw1) (by rw [hB]; exact hw2) rfl rfl
  · obtain ⟨a, c', v, s', ha, hc', hv, hw1, hex⟩ := zherm_inv_bin hex
    obtain ⟨z, s'', hz, hw2, hex⟩ := zherm_inv_lit hex
    rw [exec_skip, Option.some_inj] at hex
    subst hex
    have fr := hR.2.2.1
    simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
      IExp.eval_ofNat] at ha hw1 hw2
    rw [(zherm_readX hA hXY fr i i).1, Option.some_inj] at ha
    subst ha
    rw [fr _ _ _ hcY, hc, Option.some_inj] at hc'
    subst hc'
    have hB1 : (B i i).1 = v := by
      simp only [B, lt_irrefl, if_false, M, ScalarSem.toFloatMachine, hv, Option.getD_some]
    have hB2 : (B i i).2 = z := by
      simp only [B, lt_irrefl, if_false, M, ScalarSem.toFloatMachine]
      rw [show ((0 : ℚ)) = (0 : ℚ) from rfl, hz, Option.getD_some]
    exact ZInv.step hR i i (by rw [hB1]; exact hw1) (by rw [hB2]; exact hw2) rfl rfl

omit [DecidableEq P] [Inhabited K] in
private theorem zshift_bind {α β : Type} {o : Option α} {f : α → Option β} (R : α → Prop)
    (h₁ : ∃ a, o = some a ∧ R a) (h₂ : ∀ a, R a → ∃ b, f a = some b) :
    ∃ b, o.bind f = some b := by
  obtain ⟨a, rfl, ha⟩ := h₁
  exact h₂ a ha

omit [Inhabited K] in
private theorem zshift_write {s₀ s : Store P K} {p : P} {Y yo len k N : ℕ}
    (hY : s₀.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len) (hk : k < N)
    (hsh : s.shape = s₀.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s.read q b i = s₀.read q b i)
    (v : K) :
    ∃ s', s.write p Y (yo + k) v = some s' ∧ s'.shape = s₀.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = s₀.read q b i) ∧
      (∃ w, s'.read p Y (yo + k) = some w) ∧
      (∀ k', (∃ w, s.read p Y k' = some w) → ∃ w, s'.read p Y k' = some w) := by
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape v (hsh ▸ hY)
    (show yo + k < len by omega)
  refine ⟨s', hs', (Store.shape_of_write_eq_some hs').trans hsh,
    zherm_write_frame hs' hk hfr, ⟨v, Store.read_of_write_eq_some hs'⟩, fun k' ⟨w, hw⟩ => ?_⟩
  by_cases hkk : k' = yo + k
  · exact ⟨v, hkk ▸ Store.read_of_write_eq_some hs'⟩
  · exact ⟨w, (Store.read_of_write_eq_some_of_ne hs' (Or.inr hkk)).trans hw⟩

omit [Inhabited K] in
private theorem zshift_copy {p : P} {st σ : St P K C} {X Y xo yo len N : ℕ}
    (hYsh : st.store.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len)
    (hXY : blockDisjoint (Y, yo, N) (X, xo, N) = true) (hsh : σ.store.shape = st.store.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true →
      σ.store.read q b i = st.store.read q b i)
    (dk xk : IExp ℕ) (k : ℕ) (t : Stmt P ι ℕ ℕ) (hk : k < N) (hdk : dk.eval = yo + k)
    (hxk : xk.eval = xo + k) (ha : ∃ a, st.store.read p X (xo + k) = some a) :
    ∃ s', exec I (.seq (.instr (.copy p ⟨Y, dk⟩ ⟨X, xk⟩)) t) σ =
        exec I t { σ with store := s', cnt := σ.cnt + I.charge (.copy p) } ∧
      s'.shape = st.store.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = st.store.read q b i) ∧
      (∃ w, s'.read p Y (yo + k) = some w) ∧
      ∀ k', (∃ w, σ.store.read p Y k' = some w) → ∃ w, s'.read p Y k' = some w := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨s', hw, hrest⟩ := zshift_write hYsh hlen hk hsh hfr a
  refine ⟨s', exec_seq_instr_copy I (s := s') ?_ (by rw [hdk]; exact hw), hrest⟩
  rw [hxk, hfr _ _ _ ?_]
  · exact ha
  · simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXY ⊢
    omega

omit [Inhabited K] in
private theorem zshift_sub {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) {p : P} {c : Cell ℕ ℕ} {cv : K}
    {st σ : St P K C} {X Y xo yo len N : ℕ}
    (hYsh : st.store.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len)
    (hXY : blockDisjoint (Y, yo, N) (X, xo, N) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo, N) = true)
    (hc : st.store.read p c.buf c.idx.eval = some cv) (hsh : σ.store.shape = st.store.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true →
      σ.store.read q b i = st.store.read q b i)
    (dk xk : IExp ℕ) (k : ℕ) (t : Stmt P ι ℕ ℕ) (hk : k < N) (hdk : dk.eval = yo + k)
    (hxk : xk.eval = xo + k) (ha : ∃ a, st.store.read p X (xo + k) = some a) :
    ∃ s', exec I (.seq (.instr (.bin p .sub ⟨Y, dk⟩ ⟨X, xk⟩ c)) t) σ =
        exec I t { σ with store := s', cnt := σ.cnt + I.charge (.bin p .sub) } ∧
      s'.shape = st.store.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = st.store.read q b i) ∧
      (∃ w, s'.read p Y (yo + k) = some w) ∧
      ∀ k', (∃ w, σ.store.read p Y k' = some w) → ∃ w, s'.read p Y k' = some w := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨v, hv⟩ := hsem.bin_ok p .sub a cv trivial nofun trivial
  obtain ⟨s', hw, hrest⟩ := zshift_write hYsh hlen hk hsh hfr v
  refine ⟨s', exec_seq_instr_bin I (s := s') ?_ ?_ hv (by rw [hdk]; exact hw), hrest⟩
  · rw [hxk, hfr _ _ _ ?_]
    · exact ha
    · simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXY ⊢
      omega
  · rw [hfr _ _ _ hcY]; exact hc

omit [Inhabited K] in
private theorem zshift_lit {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) {p : P} {st σ : St P K C}
    {Y yo len N : ℕ} (hYsh : st.store.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len)
    (hsh : σ.store.shape = st.store.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true →
      σ.store.read q b i = st.store.read q b i)
    (dk : IExp ℕ) (k : ℕ) (t : Stmt P ι ℕ ℕ) (hk : k < N) (hdk : dk.eval = yo + k) :
    ∃ s', exec I (.seq (.instr (.lit p ⟨Y, dk⟩ 0)) t) σ =
        exec I t { σ with store := s', cnt := σ.cnt + I.charge (.lit p) } ∧
      s'.shape = st.store.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = st.store.read q b i) ∧
      ∀ k', (∃ w, σ.store.read p Y k' = some w) → ∃ w, s'.read p Y k' = some w := by
  obtain ⟨v, hv⟩ := hsem.lit_ok p 0 trivial
  obtain ⟨s', hw, hsh', hfr', -, hmono⟩ := zshift_write hYsh hlen hk hsh hfr v
  exact ⟨s', exec_seq_instr_lit I hv (by rw [hdk]; exact hw), hsh', hfr', hmono⟩

/-- `zhermShift` succeeds under the standard model with every value in range, when the buffer
`Y` at tag `p` is long enough. No printed source. -/
theorem exists_exec_zhermShift (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zhermShift (ι := ι) p (.const n) X xo c Y yo).run st = some st' := by
  obtain ⟨len, hYsh, hlen⟩ := hY
  have hn : ∀ i j : ℕ, i < n → j < n → 2 * (i + n * j) + 1 < 2 * (n * n) := by
    intro i j hi hj; nlinarith
  -- `Fr σ`: the shape of `st` and every cell outside the block at `Y` kept
  let Fr : St P K C → Prop := fun σ => σ.store.shape = st.store.shape ∧
    ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      σ.store.read q b i = st.store.read q b i
  -- `Up σ S`: both parts of every upper entry in `S` initialised
  let Up : St P K C → (ℕ → ℕ → Prop) → Prop := fun σ S => ∀ i j, S i j →
    (∃ v, σ.store.read p Y (yo.eval + 2 * (i + n * j)) = some v) ∧
      ∃ v, σ.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some v
  have hX : ∀ i j, i < n → j < n → (∃ a, st.store.read p X (xo.eval + 2 * (i + n * j)) = some a) ∧
      ∃ a, st.store.read p X (xo.eval + (2 * (i + n * j) + 1)) = some a :=
    fun i j hi hj => ⟨⟨_, hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨0, Nat.zero_lt_two⟩⟩,
      ⟨_, hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨1, Nat.one_lt_two⟩⟩⟩
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) _))) .skip) st =
    some st'
  rw [exec_seq_skip, exec_named, exec_seq]
  -- the strict upper triangle
  refine zshift_bind (fun σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
    ((exists_exec_loop_eq_some_of_forall I
    (fun j σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < j) ⟨⟨rfl, fun _ _ _ _ => rfl⟩,
      fun _ _ h => absurd h.2 (Nat.not_lt_zero _)⟩ (fun j hj σ ⟨hσ, hup⟩ => by
        have hj : j < n := hj
        change ∃ st', exec I (.seq (.loop _ _) .skip) σ = some st' ∧ _
        rw [exec_seq_skip]
        -- column `j`, rows `i < j`
        refine (exists_exec_loop_eq_some_of_forall I
          (fun i σ' => Fr σ' ∧ Up σ' fun i' j' => i' < j' ∧ (j' < j ∨ j' = j ∧ i' < i))
          ⟨hσ, fun i' j' h => hup i' j' ⟨h.1, by omega⟩⟩ (fun i hi σ' ⟨hσ', hup'⟩ => by
            have hi : i < j := hi
            have hk := hn i j (by omega) hj
            obtain ⟨s₁, he₁, hs₁, hf₁, hr₁, hm₁⟩ := zshift_copy hYsh hlen hXY
              hσ'.1 hσ'.2 (yo + zidx (.const n) (.var i) (.var j))
              (xo + zidx (.const n) (.var i) (.var j)) (2 * (i + n * j))
              (.seq (.instr (.copy p ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
                ⟨X, xo + zidx (.const n) (.var i) (.var j) + 1⟩)) .skip) (by omega)
              rfl rfl (hX i j (by omega) hj).1
            obtain ⟨s₂, he₂, hs₂, hf₂, hr₂, hm₂⟩ := zshift_copy hYsh hlen hXY
              (σ := { σ' with store := s₁, cnt := _ }) hs₁ hf₁
              (yo + zidx (.const n) (.var i) (.var j) + 1)
              (xo + zidx (.const n) (.var i) (.var j) + 1) (2 * (i + n * j) + 1) .skip hk
              rfl rfl (hX i j (by omega) hj).2
            refine ⟨_, he₁.trans (he₂.trans (exec_skip I _)), ⟨hs₂, hf₂⟩, fun i' j' h => ?_⟩
            by_cases hij : i' = i ∧ j' = j
            · obtain ⟨rfl, rfl⟩ := hij
              exact ⟨hm₂ _ hr₁, hr₂⟩
            · have := hup' i' j' ⟨h.1, by omega⟩
              exact ⟨hm₂ _ (hm₁ _ this.1), hm₂ _ (hm₁ _ this.2)⟩)).imp
          fun σ' ⟨h', hF', hup'⟩ => ⟨h', hF', fun i' j' h => hup' i' j' ⟨h.1, by
            simp only [IExp.eval_var]; omega⟩⟩))) fun σ₁ ⟨hσ₁, hup₁⟩ => ?_
  rw [exec_seq]
  -- the diagonal
  refine zshift_bind (fun σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
    (exists_exec_loop_eq_some_of_forall I
    (fun _ σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n) ⟨hσ₁, hup₁⟩ (fun i hi σ ⟨hσ, hup⟩ => by
        have hi : i < n := hi
        have hk := hn i i hi hi
        obtain ⟨s₁, he₁, hs₁, hf₁, -, hm₁⟩ := zshift_sub hsem hYsh hlen hXY hcY hc hσ.1 hσ.2
          (yo + zidx (.const n) (.var i) (.var i))
          (xo + zidx (.const n) (.var i) (.var i)) (2 * (i + n * i))
          (.seq (.instr (.lit p ⟨Y, yo + zidx (.const n) (.var i) (.var i) + 1⟩ 0)) .skip)
          (by omega) rfl rfl (hX i i hi hi).1
        obtain ⟨s₂, he₂, hs₂, hf₂, hm₂⟩ := zshift_lit hsem hYsh hlen
          (σ := { σ with store := s₁, cnt := _ }) hs₁ hf₁
          (yo + zidx (.const n) (.var i) (.var i) + 1) (2 * (i + n * i) + 1) .skip hk rfl
        exact ⟨_, he₁.trans (he₂.trans (exec_skip I _)), ⟨hs₂, hf₂⟩,
          fun i' j' h => ⟨hm₂ _ (hm₁ _ (hup i' j' h).1), hm₂ _ (hm₁ _ (hup i' j' h).2)⟩⟩))
    fun σ₂ ⟨hσ₂, hup₂⟩ => ?_
  -- the mirror
  refine exists_exec_zmirror p n (B := fun i j =>
    ((σ₂.store.read p Y (yo.eval + 2 * (i + n * j))).getD default,
      (σ₂.store.read p Y (yo.eval + 2 * (i + n * j) + 1)).getD default))
    (fun i j hij => ?_) hsem ⟨len, hσ₂.1 ▸ hYsh, hlen⟩
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hup₂ i j ⟨hij, j.2⟩
  simp only [hv, hw, Option.getD_some, and_self]

/-- `zhermScale` computes the machine's scaling: as
`NLAlib.Computation.holds_of_exec_zhermShift`, the block at `Y` ends holding `M.hermScale A c`.
No printed source. -/
theorem holds_of_exec_zhermScale (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    (h : exec I (zhermScale (ι := ι) p (.const n) X xo c Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermScale A cv) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  have hprog : (zhermScale (ι := ι) p (.const n) X xo c Y yo).run = .seq (.named "zhermScale"
      [.idx (.const n), .buf X, .idx xo, .cell c, .buf Y, .idx yo]
      (.seq (.loop (.const n) fun j => .seq (.loop (.var j) fun i =>
        .seq (.instr (.bin p .div ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
          ⟨X, xo + zidx (.const n) (.var i) (.var j)⟩ c))
          (.seq (.instr (.bin p .div ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
            ⟨X, xo + zidx (.const n) (.var i) (.var j) + 1⟩ c)) .skip)) .skip)
      (.seq (.loop (.const n) fun i =>
        .seq (.instr (.bin p .div ⟨Y, yo + zidx (.const n) (.var i) (.var i)⟩
          ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩ c))
          (.seq (.instr (.lit p ⟨Y, yo + zidx (.const n) (.var i) (.var i) + 1⟩ 0)) .skip))
        (zmirror (ι := ι) p (.const n) Y yo).run))) .skip := rfl
  rw [hprog, exec_seq_skip, exec_named] at h
  let B : Fin n → Fin n → K × K := fun i j =>
    if i < j then (M.div (A i j).1 cv, M.div (A i j).2 cv) else (M.div (A i i).1 cv, M.zero)
  refine (fun hL => ?_) (zherm_loops (p := p) (Y := Y) (yo := yo.eval) (B := B)
    (fun i j hij S s s₂ hR hex => ?_)
    (fun i S s s₂ hR hex => ?_) h)
  · obtain ⟨σ, hσ, h₃⟩ := hL
    have hfin := zherm_finish (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
      (normal := normal) hσ (fun i => by simp only [B, lt_irrefl, if_false]; rfl) h₃
    rwa [show M.hermScale A cv = M.hermFrom (fun i j => B i j) (fun i => (B i i).1) from
      (zherm_hermFrom_ite M _ _).symm]
  · obtain ⟨a1, c1, v1, s', hr1, hc1, hv1, hw1, hex⟩ := zherm_inv_bin hex
    obtain ⟨a2, c2, v2, s'', hr2, hc2, hv2, hw2, hex⟩ := zherm_inv_bin hex
    rw [exec_skip, Option.some_inj] at hex
    subst hex
    have fr := hR.2.2.1
    simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
      IExp.eval_ofNat] at hr1 hw1 hr2 hw2
    rw [(zherm_readX hA hXY fr i j).1, Option.some_inj] at hr1
    subst hr1
    rw [fr _ _ _ hcY, hc, Option.some_inj] at hc1
    subst hc1
    have fr' := zherm_write_frame (k := 2 * (i + n * j)) hw1
      (by have := zherm_lt i.2 j.2; omega) fr
    rw [(zherm_readX hA hXY (σ := { s with store := s' }) fr' i j).2, Option.some_inj] at hr2
    subst hr2
    rw [fr' _ _ _ hcY, hc, Option.some_inj] at hc2
    subst hc2
    have hB1 : (B i j).1 = v1 := by
      simp only [B, if_pos hij, M, ScalarSem.toFloatMachine, hv1, Option.getD_some]
    have hB2 : (B i j).2 = v2 := by
      simp only [B, if_pos hij, M, ScalarSem.toFloatMachine, hv2, Option.getD_some]
    exact ZInv.step hR i j (by rw [hB1]; exact hw1) (by rw [hB2]; exact hw2) rfl rfl
  · obtain ⟨a, c', v, s', ha, hc', hv, hw1, hex⟩ := zherm_inv_bin hex
    obtain ⟨z, s'', hz, hw2, hex⟩ := zherm_inv_lit hex
    rw [exec_skip, Option.some_inj] at hex
    subst hex
    have fr := hR.2.2.1
    simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
      IExp.eval_ofNat] at ha hw1 hw2
    rw [(zherm_readX hA hXY fr i i).1, Option.some_inj] at ha
    subst ha
    rw [fr _ _ _ hcY, hc, Option.some_inj] at hc'
    subst hc'
    have hB1 : (B i i).1 = v := by
      simp only [B, lt_irrefl, if_false, M, ScalarSem.toFloatMachine, hv, Option.getD_some]
    have hB2 : (B i i).2 = z := by
      simp only [B, lt_irrefl, if_false, M, ScalarSem.toFloatMachine]
      rw [show ((0 : ℚ)) = (0 : ℚ) from rfl, hz, Option.getD_some]
    exact ZInv.step hR i i (by rw [hB1]; exact hw1) (by rw [hB2]; exact hw2) rfl rfl

omit [DecidableEq P] in
private theorem zhermScale_disj {X Y xo yo N k : ℕ}
    (h : blockDisjoint (Y, yo, N) (X, xo, N) = true) (hk : k < N) :
    blockDisjoint (X, xo + k, 1) (Y, yo, N) = true := by
  simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h ⊢
  omega

omit [DecidableEq P] [Inhabited K] in
private theorem zhermScale_bind {α β : Type} {o : Option α} {f : α → Option β} (R : α → Prop)
    (h₁ : ∃ a, o = some a ∧ R a) (h₂ : ∀ a, R a → ∃ b, f a = some b) :
    ∃ b, o.bind f = some b := by
  obtain ⟨a, rfl, ha⟩ := h₁
  exact h₂ a ha

omit [Inhabited K] in
private theorem zhermScale_write {s₀ s : Store P K} {p : P} {Y yo len k N : ℕ}
    (hY : s₀.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len) (hk : k < N)
    (hsh : s.shape = s₀.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s.read q b i = s₀.read q b i)
    (v : K) :
    ∃ s', s.write p Y (yo + k) v = some s' ∧ s'.shape = s₀.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = s₀.read q b i) ∧
      (∃ w, s'.read p Y (yo + k) = some w) ∧
      (∀ k', (∃ w, s.read p Y k' = some w) → ∃ w, s'.read p Y k' = some w) := by
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape v (hsh ▸ hY)
    (show yo + k < len by omega)
  refine ⟨s', hs', (Store.shape_of_write_eq_some hs').trans hsh, fun q b i hb => ?_,
    ⟨v, Store.read_of_write_eq_some hs'⟩, fun k' ⟨w, hw⟩ => ?_⟩
  · refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans (hfr q b i hb)
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
    omega
  · by_cases hkk : k' = yo + k
    · exact ⟨v, hkk ▸ Store.read_of_write_eq_some hs'⟩
    · exact ⟨w, (Store.read_of_write_eq_some_of_ne hs' (Or.inr hkk)).trans hw⟩

omit [Inhabited K] in
private theorem zhermScale_div {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) {p : P} {c : Cell ℕ ℕ} {cv : K}
    (hcv : dec p cv ≠ 0) {st σ : St P K C} {X Y xo yo len N : ℕ}
    (hYsh : st.store.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len)
    (hXY : blockDisjoint (Y, yo, N) (X, xo, N) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo, N) = true)
    (hc : st.store.read p c.buf c.idx.eval = some cv) (hsh : σ.store.shape = st.store.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true →
      σ.store.read q b i = st.store.read q b i)
    (dk xk : IExp ℕ) (k : ℕ) (t : Stmt P ι ℕ ℕ) (hk : k < N) (hdk : dk.eval = yo + k)
    (hxk : xk.eval = xo + k) (ha : ∃ a, st.store.read p X (xo + k) = some a) :
    ∃ s', exec I (.seq (.instr (.bin p .div ⟨Y, dk⟩ ⟨X, xk⟩ c)) t) σ =
        exec I t { σ with store := s', cnt := σ.cnt + I.charge (.bin p .div) } ∧
      s'.shape = st.store.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = st.store.read q b i) ∧
      (∃ w, s'.read p Y (yo + k) = some w) ∧
      ∀ k', (∃ w, σ.store.read p Y k' = some w) → ∃ w, s'.read p Y k' = some w := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨v, hv⟩ := hsem.bin_ok p .div a cv trivial (fun _ => hcv) trivial
  obtain ⟨s', hw, hrest⟩ := zhermScale_write hYsh hlen hk hsh hfr v
  refine ⟨s', exec_seq_instr_bin I (s := s') ?_ ?_ hv (by rw [hdk]; exact hw), hrest⟩
  · rw [hxk, hfr _ _ _ (zhermScale_disj hXY hk)]; exact ha
  · rw [hfr _ _ _ hcY]; exact hc

omit [Inhabited K] in
private theorem zhermScale_lit {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) {p : P} {st σ : St P K C}
    {Y yo len N : ℕ} (hYsh : st.store.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len)
    (hsh : σ.store.shape = st.store.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true →
      σ.store.read q b i = st.store.read q b i)
    (dk : IExp ℕ) (k : ℕ) (t : Stmt P ι ℕ ℕ) (hk : k < N) (hdk : dk.eval = yo + k) :
    ∃ s', exec I (.seq (.instr (.lit p ⟨Y, dk⟩ 0)) t) σ =
        exec I t { σ with store := s', cnt := σ.cnt + I.charge (.lit p) } ∧
      s'.shape = st.store.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = st.store.read q b i) ∧
      ∀ k', (∃ w, σ.store.read p Y k' = some w) → ∃ w, s'.read p Y k' = some w := by
  obtain ⟨v, hv⟩ := hsem.lit_ok p 0 trivial
  obtain ⟨s', hw, hsh', hfr', -, hmono⟩ := zhermScale_write hYsh hlen hk hsh hfr v
  exact ⟨s', exec_seq_instr_lit I hv (by rw [hdk]; exact hw), hsh', hfr', hmono⟩

/-- `zhermScale` succeeds under the standard model with every value in range, when $c$ decodes
to a nonzero value and the buffer `Y` at tag `p` is long enough. No printed source. -/
theorem exists_exec_zhermScale (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hcv : dec p cv ≠ 0)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zhermScale (ι := ι) p (.const n) X xo c Y yo).run st = some st' := by
  obtain ⟨len, hYsh, hlen⟩ := hY
  have hn : ∀ i j : ℕ, i < n → j < n → 2 * (i + n * j) + 1 < 2 * (n * n) := by
    intro i j hi hj; nlinarith
  -- `Fr σ`: the shape of `st` and every cell outside the block at `Y` kept
  let Fr : St P K C → Prop := fun σ => σ.store.shape = st.store.shape ∧
    ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      σ.store.read q b i = st.store.read q b i
  -- `Up σ S`: both parts of every upper entry in `S` initialised
  let Up : St P K C → (ℕ → ℕ → Prop) → Prop := fun σ S => ∀ i j, S i j →
    (∃ v, σ.store.read p Y (yo.eval + 2 * (i + n * j)) = some v) ∧
      ∃ v, σ.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some v
  have hX : ∀ i j, i < n → j < n → (∃ a, st.store.read p X (xo.eval + 2 * (i + n * j)) = some a) ∧
      ∃ a, st.store.read p X (xo.eval + (2 * (i + n * j) + 1)) = some a :=
    fun i j hi hj => ⟨⟨_, hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨0, Nat.zero_lt_two⟩⟩,
      ⟨_, hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨1, Nat.one_lt_two⟩⟩⟩
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) _))) .skip) st =
    some st'
  rw [exec_seq_skip, exec_named, exec_seq]
  -- the strict upper triangle
  refine zhermScale_bind (fun σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
    ((exists_exec_loop_eq_some_of_forall I
    (fun j σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < j) ⟨⟨rfl, fun _ _ _ _ => rfl⟩,
      fun _ _ h => absurd h.2 (Nat.not_lt_zero _)⟩ (fun j hj σ ⟨hσ, hup⟩ => by
        have hj : j < n := hj
        change ∃ st', exec I (.seq (.loop _ _) .skip) σ = some st' ∧ _
        rw [exec_seq_skip]
        -- column `j`, rows `i < j`
        refine (exists_exec_loop_eq_some_of_forall I
          (fun i σ' => Fr σ' ∧ Up σ' fun i' j' => i' < j' ∧ (j' < j ∨ j' = j ∧ i' < i))
          ⟨hσ, fun i' j' h => hup i' j' ⟨h.1, by omega⟩⟩ (fun i hi σ' ⟨hσ', hup'⟩ => by
            have hi : i < j := hi
            have hk := hn i j (by omega) hj
            obtain ⟨s₁, he₁, hs₁, hf₁, hr₁, hm₁⟩ := zhermScale_div hsem hcv hYsh hlen hXY hcY hc
              hσ'.1 hσ'.2 (yo + zidx (.const n) (.var i) (.var j))
              (xo + zidx (.const n) (.var i) (.var j)) (2 * (i + n * j))
              (.seq (.instr (.bin p .div ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
                ⟨X, xo + zidx (.const n) (.var i) (.var j) + 1⟩ c)) .skip) (by omega)
              rfl rfl (hX i j (by omega) hj).1
            obtain ⟨s₂, he₂, hs₂, hf₂, hr₂, hm₂⟩ := zhermScale_div hsem hcv hYsh hlen hXY hcY hc
              (σ := { σ' with store := s₁, cnt := _ }) hs₁ hf₁
              (yo + zidx (.const n) (.var i) (.var j) + 1)
              (xo + zidx (.const n) (.var i) (.var j) + 1) (2 * (i + n * j) + 1) .skip hk
              rfl rfl (hX i j (by omega) hj).2
            refine ⟨_, he₁.trans (he₂.trans (exec_skip I _)), ⟨hs₂, hf₂⟩, fun i' j' h => ?_⟩
            by_cases hij : i' = i ∧ j' = j
            · obtain ⟨rfl, rfl⟩ := hij
              exact ⟨hm₂ _ hr₁, hr₂⟩
            · have := hup' i' j' ⟨h.1, by omega⟩
              exact ⟨hm₂ _ (hm₁ _ this.1), hm₂ _ (hm₁ _ this.2)⟩)).imp
          fun σ' ⟨h', hF', hup'⟩ => ⟨h', hF', fun i' j' h => hup' i' j' ⟨h.1, by
            simp only [IExp.eval_var]; omega⟩⟩))) fun σ₁ ⟨hσ₁, hup₁⟩ => ?_
  rw [exec_seq]
  -- the diagonal
  refine zhermScale_bind (fun σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
    (exists_exec_loop_eq_some_of_forall I
    (fun _ σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n) ⟨hσ₁, hup₁⟩ (fun i hi σ ⟨hσ, hup⟩ => by
        have hi : i < n := hi
        have hk := hn i i hi hi
        obtain ⟨s₁, he₁, hs₁, hf₁, -, hm₁⟩ := zhermScale_div hsem hcv hYsh hlen hXY hcY hc hσ.1 hσ.2
          (yo + zidx (.const n) (.var i) (.var i))
          (xo + zidx (.const n) (.var i) (.var i)) (2 * (i + n * i))
          (.seq (.instr (.lit p ⟨Y, yo + zidx (.const n) (.var i) (.var i) + 1⟩ 0)) .skip)
          (by omega) rfl rfl (hX i i hi hi).1
        obtain ⟨s₂, he₂, hs₂, hf₂, hm₂⟩ := zhermScale_lit hsem hYsh hlen
          (σ := { σ with store := s₁, cnt := _ }) hs₁ hf₁
          (yo + zidx (.const n) (.var i) (.var i) + 1) (2 * (i + n * i) + 1) .skip hk rfl
        exact ⟨_, he₁.trans (he₂.trans (exec_skip I _)), ⟨hs₂, hf₂⟩,
          fun i' j' h => ⟨hm₂ _ (hm₁ _ (hup i' j' h).1), hm₂ _ (hm₁ _ (hup i' j' h).2)⟩⟩))
    fun σ₂ ⟨hσ₂, hup₂⟩ => ?_
  -- the mirror
  refine exists_exec_zmirror p n (B := fun i j =>
    ((σ₂.store.read p Y (yo.eval + 2 * (i + n * j))).getD default,
      (σ₂.store.read p Y (yo.eval + 2 * (i + n * j) + 1)).getD default))
    (fun i j hij => ?_) hsem ⟨len, hσ₂.1 ▸ hYsh, hlen⟩
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hup₂ i j ⟨hij, j.2⟩
  simp only [hv, hw, Option.getD_some, and_self]

end NLAlib.Computation
