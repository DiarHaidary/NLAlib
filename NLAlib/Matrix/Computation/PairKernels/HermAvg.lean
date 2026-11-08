/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PairKernels.Hermitian

/-!
# Complex-pair kernels: the Hermitian average

The rounded specification of `NLAlib.Computation.zhermAvg`, the Hermitian part $(\mathbf{A} +
c\,\mathbf{B})/2$ of the Newton–Schulz step: a successful run writes the machine's `hermAvg`, and
the run succeeds when its operations do.

## Main results

* `NLAlib.Computation.holds_of_exec_zhermAvg`: what a successful run computes.
* `NLAlib.Computation.exists_exec_zhermAvg`: when the run succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

omit [DecidableEq P] [Inhabited K] in
/-- The statement tree of `zhermAvg`: the strict upper triangle, the diagonal, the mirror. -/
private theorem zhermAvg_run (p : P) (n : ℕ) (X Y : ℕ) (xo yo : IExp ℕ) (c : Cell ℕ ℕ) :
    (zhermAvg (ι := ι) p (.const n) X xo c Y yo).run = .seq (.named "zhermAvg"
    [.idx (.const n), .buf X, .idx xo, .cell c, .buf Y, .idx yo]
    (.seq (.loop (.const n) fun j => .seq (.loop (.var j) fun i =>
      .seq (.instr (.bin p .add ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
        ⟨X, xo + zidx (.const n) (.var i) (.var j)⟩ ⟨X, xo + zidx (.const n) (.var j) (.var i)⟩))
      (.seq (.instr (.bin p .div ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
        ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩ c))
      (.seq (.instr (.bin p .sub ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
        ⟨X, xo + zidx (.const n) (.var i) (.var j) + 1⟩
        ⟨X, xo + zidx (.const n) (.var j) (.var i) + 1⟩))
      (.seq (.instr (.bin p .div ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
        ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩ c)) .skip)))) .skip)
    (.seq (.loop (.const n) fun i =>
      .seq (.instr (.bin p .add ⟨Y, yo + zidx (.const n) (.var i) (.var i)⟩
        ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩ ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩))
      (.seq (.instr (.bin p .div ⟨Y, yo + zidx (.const n) (.var i) (.var i)⟩
        ⟨Y, yo + zidx (.const n) (.var i) (.var i)⟩ c))
      (.seq (.instr (.lit p ⟨Y, yo + zidx (.const n) (.var i) (.var i) + 1⟩ 0)) .skip)))
      (zmirror (ι := ι) p (.const n) Y yo).run))) .skip := rfl

/-- `zhermAvg` computes the machine's Hermitian part: a successful run of
`NLAlib.Computation.zhermAvg` from a state whose block at `X` holds the complex $n \times n$
matrix $\mathbf{A}$ and whose cell `c` holds $c$, into a block at `Y` disjoint from the block at
`X` and from `c`, ends with the block at `Y` holding `M.hermAvg A c` for the machine `M` of the
semantics at `p`, every cell outside it unchanged, the same store shape and the same tape
positions. No printed source. -/
theorem holds_of_exec_zhermAvg (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    (h : exec I (zhermAvg (ι := ι) p (.const n) X xo c Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermAvg A cv) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  rw [zhermAvg_run, exec_seq_skip, exec_named] at h
  let B : Fin n → Fin n → K × K := fun i j =>
    if i < j then (M.div (M.add (A i j).1 (A j i).1) cv, M.div (M.sub (A i j).2 (A j i).2) cv)
    else (M.div (M.add (A i i).1 (A i i).1) cv, M.zero)
  refine (fun hL => ?_) (zherm_loops (p := p) (Y := Y) (yo := yo.eval) (B := B)
    (fun i j hij S s s₂ hR hex => ?_)
    (fun i S s s₂ hR hex => ?_) h)
  · obtain ⟨σ, hσ, h₃⟩ := hL
    have hfin := zherm_finish (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
      (normal := normal) hσ (fun i => by simp only [B, lt_irrefl, if_false]; rfl) h₃
    rwa [show M.hermAvg A cv = M.hermFrom (fun i j => B i j) (fun i => (B i i).1) from
      (hermFrom_ite_eq M _ _).symm]
  · have hk : 2 * (i + n * j) + 1 < 2 * (n * n) := by
      have := Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2; omega
    obtain ⟨a1, b1, v1, s₁, ha1, hb1, hv1, hw1, hex⟩ := zherm_inv_bin hex
    obtain ⟨a2, c2, v2, s₂', ha2, hc2, hv2, hw2, hex⟩ := zherm_inv_bin hex
    obtain ⟨a3, b3, v3, s₃, ha3, hb3, hv3, hw3, hex⟩ := zherm_inv_bin hex
    obtain ⟨a4, c4, v4, s₄, ha4, hc4, hv4, hw4, hex⟩ := zherm_inv_bin hex
    rw [exec_skip, Option.some_inj] at hex
    subst hex
    have fr := hR.2.2.1
    simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
      IExp.eval_ofNat] at ha1 hb1 hw1 ha2 hw2 ha3 hb3 hw3 ha4 hw4
    rw [(zherm_readX hA hXY fr i j).1, Option.some_inj] at ha1
    rw [(zherm_readX hA hXY fr j i).1, Option.some_inj] at hb1
    subst ha1 hb1
    rw [Store.read_of_write_eq_some hw1, Option.some_inj] at ha2
    subst ha2
    have fr1 := read_eq_of_write_eq_some_of_lt (k := 2 * (i + n * j)) hw1 (by omega) fr
    rw [fr1 _ _ _ hcY, hc, Option.some_inj] at hc2
    subst hc2
    rw [Store.write_of_write_eq_some hw1] at hw2
    have fr2 := read_eq_of_write_eq_some_of_lt (k := 2 * (i + n * j)) hw2 (by omega) fr
    rw [(zherm_readX hA hXY (σ := { s with store := s₂' }) fr2 i j).2, Option.some_inj] at ha3
    rw [(zherm_readX hA hXY (σ := { s with store := s₂' }) fr2 j i).2, Option.some_inj] at hb3
    subst ha3 hb3
    rw [Store.read_of_write_eq_some hw3, Option.some_inj] at ha4
    subst ha4
    have fr3 := read_eq_of_write_eq_some_of_lt (k := 2 * (i + n * j) + 1) hw3 (by omega) fr2
    rw [fr3 _ _ _ hcY, hc, Option.some_inj] at hc4
    subst hc4
    rw [Store.write_of_write_eq_some hw3] at hw4
    have hB1 : (B i j).1 = v2 := by
      simp only [B, if_pos hij, M, ScalarSem.toFloatMachine, hv1, hv2, Option.getD_some]
    have hB2 : (B i j).2 = v4 := by
      simp only [B, if_pos hij, M, ScalarSem.toFloatMachine, hv3, hv4, Option.getD_some]
    exact ZInv.step hR i j (by rw [hB1]; exact hw2) (by rw [hB2]; exact hw4) rfl rfl
  · have hk : 2 * (i + n * i) + 1 < 2 * (n * n) := by
      have := Nat.add_mul_lt_mul_of_lt_of_lt i.2 i.2; omega
    obtain ⟨a1, b1, v1, s₁, ha1, hb1, hv1, hw1, hex⟩ := zherm_inv_bin hex
    obtain ⟨a2, c2, v2, s₂', ha2, hc2, hv2, hw2, hex⟩ := zherm_inv_bin hex
    obtain ⟨z, s₃, hz, hw3, hex⟩ := zherm_inv_lit hex
    rw [exec_skip, Option.some_inj] at hex
    subst hex
    have fr := hR.2.2.1
    simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
      IExp.eval_ofNat] at ha1 hb1 hw1 ha2 hw2 hw3
    rw [(zherm_readX hA hXY fr i i).1, Option.some_inj] at ha1 hb1
    subst ha1 hb1
    rw [Store.read_of_write_eq_some hw1, Option.some_inj] at ha2
    subst ha2
    have fr1 := read_eq_of_write_eq_some_of_lt (k := 2 * (i + n * i)) hw1 (by omega) fr
    rw [fr1 _ _ _ hcY, hc, Option.some_inj] at hc2
    subst hc2
    rw [Store.write_of_write_eq_some hw1] at hw2
    have hB1 : (B i i).1 = v2 := by
      simp only [B, lt_irrefl, if_false, M, ScalarSem.toFloatMachine, hv1, hv2, Option.getD_some]
    have hB2 : (B i i).2 = z := by
      simp only [B, lt_irrefl, if_false, M, ScalarSem.toFloatMachine]
      rw [show ((0 : ℚ)) = (0 : ℚ) from rfl, hz, Option.getD_some]
    exact ZInv.step hR i i (by rw [hB1]; exact hw2) (by rw [hB2]; exact hw3) rfl rfl

omit [Inhabited K] in
private theorem zhermAvg_entry {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) {p : P} {n X Y : ℕ} {xo yo : IExp ℕ}
    {c : Cell ℕ ℕ} {cv : K} (hcv : dec p cv ≠ 0) {st σ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true) {len : ℕ}
    (hYsh : st.store.shape[Y]? = some (p, len)) (hlen : yo.eval + 2 * (n * n) ≤ len)
    (hs₀ : σ.store.shape = st.store.shape)
    (hf₀ : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      σ.store.read q b i = st.store.read q b i) {i j : ℕ} (hij : i < j) (hj : j < n) :
    ∃ σ', exec I (.seq (.instr (.bin p .add ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
          ⟨X, xo + zidx (.const n) (.var i) (.var j)⟩ ⟨X, xo + zidx (.const n) (.var j) (.var i)⟩))
        (.seq (.instr (.bin p .div ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
          ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩ c))
        (.seq (.instr (.bin p .sub ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
          ⟨X, xo + zidx (.const n) (.var i) (.var j) + 1⟩
          ⟨X, xo + zidx (.const n) (.var j) (.var i) + 1⟩))
        (.seq (.instr (.bin p .div ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
          ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩ c)) .skip)))) σ = some σ' ∧
      σ'.store.shape = st.store.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        σ'.store.read q b i = st.store.read q b i) ∧
      ((∃ v, σ'.store.read p Y (yo.eval + 2 * (i + n * j)) = some v) ∧
        ∃ v, σ'.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some v) ∧
      ∀ k', (∃ w, σ.store.read p Y k' = some w) → ∃ w, σ'.store.read p Y k' = some w := by
  have hn : ∀ i j : ℕ, i < n → j < n → 2 * (i + n * j) + 1 < 2 * (n * n) := by
    intro i j hi hj; nlinarith
  have hX : ∀ s : Store P K, (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      s.read q b i = st.store.read q b i) → ∀ i j, i < n → j < n →
      (∃ a, s.read p X (xo.eval + 2 * (i + n * j)) = some a) ∧
      ∃ a, s.read p X (xo.eval + (2 * (i + n * j) + 1)) = some a := fun s hs i j hi hj =>
    ⟨⟨_, (hs _ _ _ (blockDisjoint_add_of_blockDisjoint_of_lt hXY
        (by have := hn i j hi hj; omega))).trans
        (hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨0, Nat.zero_lt_two⟩)⟩,
      ⟨_, (hs _ _ _ (blockDisjoint_add_of_blockDisjoint_of_lt hXY (hn i j hi hj))).trans
        (hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨1, Nat.one_lt_two⟩)⟩⟩
  have hC : ∀ s : Store P K, (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      s.read q b i = st.store.read q b i) →
      ∃ c', s.read p c.buf c.idx.eval = some c' ∧ (BinOp.div = .div → dec p c' ≠ 0) :=
    fun s hs => ⟨cv, (hs _ _ _ hcY).trans hc, fun _ => hcv⟩
  have hk := hn i j (by omega) hj
  obtain ⟨s₁, he₁, hs₁, hf₁, hr₁, hm₁⟩ := exists_exec_seq_instr_bin_eq hsem (b := .add)
    trivial hYsh hlen hs₀ hf₀
    (yo + zidx (.const n) (.var i) (.var j)) ⟨X, xo + zidx (.const n) (.var i) (.var j)⟩
    ⟨X, xo + zidx (.const n) (.var j) (.var i)⟩ (2 * (i + n * j)) (by omega) rfl
    (hX _ hf₀ i j (by omega) hj).1
    (((hX _ hf₀ j i hj (by omega)).1).imp fun _ h => ⟨h, nofun⟩)
  obtain ⟨s₂, he₂, hs₂, hf₂, hr₂, hm₂⟩ := exists_exec_seq_instr_bin_eq hsem (b := .div)
    trivial hYsh hlen (σ := { σ with store := s₁, cnt := _ }) hs₁ hf₁
    (yo + zidx (.const n) (.var i) (.var j)) ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
    c (2 * (i + n * j)) (by omega) rfl hr₁ (hC _ hf₁)
  obtain ⟨s₃, he₃, hs₃, hf₃, hr₃, hm₃⟩ := exists_exec_seq_instr_bin_eq hsem (b := .sub)
    trivial hYsh hlen (σ := { σ with store := s₂, cnt := _ }) hs₂ hf₂
    (yo + zidx (.const n) (.var i) (.var j) + 1)
    ⟨X, xo + zidx (.const n) (.var i) (.var j) + 1⟩
    ⟨X, xo + zidx (.const n) (.var j) (.var i) + 1⟩ (2 * (i + n * j) + 1) hk rfl
    (hX _ hf₂ i j (by omega) hj).2
    (((hX _ hf₂ j i hj (by omega)).2).imp fun _ h => ⟨h, nofun⟩)
  obtain ⟨s₄, he₄, hs₄, hf₄, hr₄, hm₄⟩ := exists_exec_seq_instr_bin_eq hsem (b := .div)
    trivial hYsh hlen (σ := { σ with store := s₃, cnt := _ }) hs₃ hf₃
    (yo + zidx (.const n) (.var i) (.var j) + 1)
    ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩ c (2 * (i + n * j) + 1) hk rfl
    hr₃ (hC _ hf₃)
  exact ⟨_, (he₁ _).trans ((he₂ _).trans ((he₃ _).trans ((he₄ _).trans (exec_skip I _)))),
    hs₄, hf₄, ⟨hm₄ _ (hm₃ _ hr₂), hr₄⟩, fun k' h => hm₄ _ (hm₃ _ (hm₂ _ (hm₁ _ h)))⟩

/-- `zhermAvg` succeeds under the standard model with every value in range, when $c$ decodes
to a nonzero value and the buffer `Y` at tag `p` is long enough (every addition, subtraction,
negation and literal then succeeds, and every division by $c$). No printed source. -/
theorem exists_exec_zhermAvg (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hcv : dec p cv ≠ 0)
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zhermAvg (ι := ι) p (.const n) X xo c Y yo).run st = some st' := by
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
  -- the reads of `X` and `c` survive in every framed store
  have hX : ∀ s : Store P K, (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      s.read q b i = st.store.read q b i) → ∀ i j, i < n → j < n →
      (∃ a, s.read p X (xo.eval + 2 * (i + n * j)) = some a) ∧
      ∃ a, s.read p X (xo.eval + (2 * (i + n * j) + 1)) = some a := fun s hs i j hi hj =>
    ⟨⟨_, (hs _ _ _ (blockDisjoint_add_of_blockDisjoint_of_lt hXY
        (by have := hn i j hi hj; omega))).trans
        (hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨0, Nat.zero_lt_two⟩)⟩,
      ⟨_, (hs _ _ _ (blockDisjoint_add_of_blockDisjoint_of_lt hXY (hn i j hi hj))).trans
        (hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨1, Nat.one_lt_two⟩)⟩⟩
  have hC : ∀ s : Store P K, (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      s.read q b i = st.store.read q b i) →
      ∃ c', s.read p c.buf c.idx.eval = some c' ∧ (BinOp.div = .div → dec p c' ≠ 0) :=
    fun s hs => ⟨cv, (hs _ _ _ hcY).trans hc, fun _ => hcv⟩
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) _))) .skip) st =
    some st'
  rw [exec_seq_skip, exec_named, exec_seq]
  -- the strict upper triangle
  refine Option.exists_bind_eq_some_of_exists (fun σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
    ((exists_exec_loop_eq_some_of_forall I
    (fun j σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < j) ⟨⟨rfl, fun _ _ _ _ => rfl⟩,
      fun _ _ h => absurd h.2 (Nat.not_lt_zero _)⟩ (fun j hj σ ⟨hσ, hup⟩ => by
        have hj : j < n := hj
        change ∃ st', exec I (.seq (.loop _ _) .skip) σ = some st' ∧ _
        rw [exec_seq_skip]
        -- column `j`, rows `i < j`
        refine (exists_exec_loop_eq_some_of_forall I
          (fun i σ' => Fr σ' ∧ Up σ' fun i' j' => i' < j' ∧ (j' < j ∨ j' = j ∧ i' < i))
          ⟨hσ, fun i' j' h => hup i' j' ⟨h.1, by omega⟩⟩ (fun i hi σ' ⟨⟨hs₀, hf₀⟩, hup'⟩ => by
            obtain ⟨σ'', he, hs, hf, hr, hm⟩ := zhermAvg_entry hsem hcv hA hc hXY hcY hYsh hlen
              hs₀ hf₀ (show i < j from hi) hj
            refine ⟨σ'', he, ⟨hs, hf⟩, fun i' j' h => ?_⟩
            by_cases hij : i' = i ∧ j' = j
            · obtain ⟨rfl, rfl⟩ := hij
              exact hr
            · have := hup' i' j' ⟨h.1, by omega⟩
              exact ⟨hm _ this.1, hm _ this.2⟩)).imp
          fun σ' ⟨h', hF', hup'⟩ => ⟨h', hF', fun i' j' h => hup' i' j' ⟨h.1, by
            simp only [IExp.eval_var]; omega⟩⟩))) fun σ₁ ⟨hσ₁, hup₁⟩ => ?_
  rw [exec_seq]
  -- the diagonal
  refine Option.exists_bind_eq_some_of_exists (fun σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
    (exists_exec_loop_eq_some_of_forall I (fun _ σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
      ⟨hσ₁, hup₁⟩ (fun i hi σ ⟨⟨hs₀, hf₀⟩, hup⟩ => by
        have hi : i < n := hi
        have hk := hn i i hi hi
        obtain ⟨s₁, he₁, hs₁, hf₁, hr₁, hm₁⟩ := exists_exec_seq_instr_bin_eq hsem (b := .add)
          trivial hYsh hlen hs₀ hf₀ (yo + zidx (.const n) (.var i) (.var i))
          ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩ ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩
          (2 * (i + n * i)) (by omega) rfl
          (hX _ hf₀ i i hi hi).1 (((hX _ hf₀ i i hi hi).1).imp fun _ h => ⟨h, nofun⟩)
        obtain ⟨s₂, he₂, hs₂, hf₂, -, hm₂⟩ := exists_exec_seq_instr_bin_eq hsem (b := .div)
          trivial hYsh hlen (σ := { σ with store := s₁, cnt := _ }) hs₁ hf₁
          (yo + zidx (.const n) (.var i) (.var i)) ⟨Y, yo + zidx (.const n) (.var i) (.var i)⟩
          c (2 * (i + n * i)) (by omega) rfl hr₁ (hC _ hf₁)
        obtain ⟨s₃, he₃, hs₃, hf₃, hm₃⟩ := exists_exec_seq_instr_lit_eq hsem hYsh hlen
          (σ := { σ with store := s₂, cnt := _ }) hs₂ hf₂
          (yo + zidx (.const n) (.var i) (.var i) + 1) (2 * (i + n * i) + 1) hk rfl
        exact ⟨_, (he₁ _).trans ((he₂ _).trans ((he₃ _).trans (exec_skip I _))), ⟨hs₃, hf₃⟩,
          fun i' j' h => ⟨hm₃ _ (hm₂ _ (hm₁ _ (hup i' j' h).1)),
            hm₃ _ (hm₂ _ (hm₁ _ (hup i' j' h).2))⟩⟩))
    fun σ₂ ⟨hσ₂, hup₂⟩ => ?_
  -- the mirror
  refine exists_exec_zmirror p n (B := fun i j =>
    ((σ₂.store.read p Y (yo.eval + 2 * (i + n * j))).getD default,
      (σ₂.store.read p Y (yo.eval + 2 * (i + n * j) + 1)).getD default))
    (fun i j hij => ?_) hsem ⟨len, hσ₂.1 ▸ hYsh, hlen⟩
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hup₂ i j ⟨hij, j.2⟩
  simp only [hv, hw, Option.getD_some, and_self]

end NLAlib.Computation
