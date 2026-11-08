/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Matrix.Computation.InterpMachine
public import NLAlib.Computation.Loops

/-!
# Complex-pair kernels: copies, literals, negation and the Hermitian completion

The rounded specifications of the complex kernels of `NLAlib/Computation/BLAS.lean` on interleaved
pairs (`NLAlib.Computation.pairLayout`). Under any interpretation, a successful run of a kernel on
blocks that hold stored complex matrices (`NLAlib.Computation.EntryLayout.Holds`) ends with the
output block holding exactly the result of the corresponding operation of the machine of the
semantics (`NLAlib.Computation.ScalarSem.toFloatMachine`), one rounding per real operation, and
every other cell unchanged; and the run succeeds when the operations it performs succeed. With the
exact specifications of `NLAlib/Matrix/Computation/InterpMachine.lean` and the machine contract,
these give the exact and the rounded behaviour of each kernel.

This file treats the copy, the zero block, negation and the Hermitian completion `zmirror`; the
other kernels are in the files `NLAlib/Matrix/Computation/PairKernels/*.lean`.

## Main results

* `NLAlib.Computation.holds_of_exec_zcopy`, `NLAlib.Computation.holds_of_exec_zzero`,
  `NLAlib.Computation.holds_of_exec_zneg`, `NLAlib.Computation.holds_of_exec_zmirror`: what a
  successful run computes.
* `NLAlib.Computation.exists_exec_zcopy`, `NLAlib.Computation.exists_exec_zzero`,
  `NLAlib.Computation.exists_exec_zneg`, `NLAlib.Computation.exists_exec_zmirror`: when the run
  succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### Copies and literals -/

omit [Inhabited K] in
/-- `zcopy` copies: a successful run of `NLAlib.Computation.zcopy` from a state whose block at
`X` holds the complex $m \times n$ matrix $\mathbf{A}$, into a block at `Y` disjoint from it,
ends with the block at `Y` holding $\mathbf{A}$, every cell outside it unchanged, the same store
shape and the same tape positions. No printed source. -/
theorem holds_of_exec_zcopy (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {st st' : St P K C}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true)
    (h : exec I (zcopy (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval A ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hrun : (zcopy (ι := ι) p (.const m) (.const n) X xo Y yo).run = .seq (.named "zcopy"
      [.idx (.const m), .idx (.const n), .buf X, .idx xo, .buf Y, .idx yo]
      (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.instr (.copy p ⟨Y, yo + .var w⟩ ⟨X, xo + .var w⟩)) .skip) .skip)) .skip := rfl
  rw [hrun, exec_seq_skip, exec_named, exec_seq_skip] at h
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hXY
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I
    (fun w s => s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
      (∀ k < w, s.store.read p Y (yo.eval + k) = st.store.read p X (xo.eval + k)) ∧
      ∀ q b i, (b ≠ Y ∨ i < yo.eval ∨ yo.eval + w ≤ i) →
        s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h)
  · obtain ⟨hsh, hpos, hY, hfr⟩ := hR
    simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hY hfr
    refine ⟨fun i j t => ?_, fun q b i hb => hfr q b i ?_, hsh, hpos⟩
    · have hj := Nat.mul_le_mul_left m (show j.1 + 1 ≤ n from j.2)
      have ht : t.1 < 2 := t.2
      rw [Nat.mul_succ] at hj
      have hk : 2 * (i.1 + m * j.1) + t.1 < 2 * (m * n) := by omega
      exact (hY _ hk).trans (hA i j t)
    · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hb
      by_cases hbY : b = Y
      · exact Or.inr (by omega)
      · exact Or.inl hbY
  rintro w hw s₁ s₂ ⟨hsh, hpos, hY, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  simp only [IExp.eval_add, IExp.eval_var] at hv hw'
  simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hw
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hpos, fun k hk => ?_,
    fun q b i hb => (Store.read_of_write_eq_some_of_ne hw' ?_).trans (hfr q b i ?_)⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact (Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega))).trans (hY k hk)
    · refine (Store.read_of_write_eq_some hw').trans (hv.symm.trans (hfr _ _ _ ?_))
      by_cases hb : X = Y
      · exact Or.inr (by omega)
      · exact Or.inl hb
  · by_cases hbY : b = Y
    · exact Or.inr (by omega)
    · exact Or.inl hbY
  · omega

omit [Inhabited K] in
/-- `zcopy` succeeds from a state whose block at `X` holds a complex $m \times n$ matrix and
whose buffer `Y` at tag `p` is long enough. No printed source. -/
theorem exists_exec_zcopy (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {st : St P K C}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (m * n) ≤ len) :
    ∃ st', exec I (zcopy (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st' := by
  obtain ⟨len, hYs, hlen⟩ := hY
  have hX : ∀ k < 2 * (m * n), ∃ v, st.store.read p X (xo.eval + k) = some v := by
    intro k hk
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
    have e : 2 * (k / 2 % m + m * (k / 2 / m)) + k % 2 = k := by rw [Nat.mod_add_div]; omega
    exact ⟨_, e ▸ hA ⟨_, Nat.mod_lt _ hm⟩ ⟨_, Nat.div_lt_of_lt_mul (by omega)⟩
      ⟨_, Nat.mod_lt _ two_pos⟩⟩
  have hrun : (zcopy (ι := ι) p (.const m) (.const n) X xo Y yo).run = .seq (.named "zcopy"
      [.idx (.const m), .idx (.const n), .buf X, .idx xo, .buf Y, .idx yo]
      (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.instr (.copy p ⟨Y, yo + .var w⟩ ⟨X, xo + .var w⟩)) .skip) .skip)) .skip := rfl
  rw [hrun, exec_seq_skip, exec_named, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I
    (fun _ s => s.store.shape = st.store.shape ∧ ∀ k < 2 * (m * n),
      s.store.read p X (xo.eval + k) = st.store.read p X (xo.eval + k))
    ⟨rfl, fun _ _ => rfl⟩ ?_).imp fun _ h => h.1
  rintro w hw s ⟨hsh, hs⟩
  simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hw
  obtain ⟨v, hv⟩ := hX w hw
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape v (hsh ▸ hYs)
    (i := yo.eval + w) (by omega)
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hXY
  refine ⟨_, (exec_seq_instr_copy I (by exact (hs w hw).trans hv) hs').trans (exec_skip I _),
    (Store.shape_of_write_eq_some hs').trans hsh, fun k hk => ?_⟩
  refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans (hs k hk)
  by_cases hb : X = Y
  · exact Or.inr (by omega)
  · exact Or.inl hb

/-- `zzero` writes the stored zero matrix: a successful run of `NLAlib.Computation.zzero`
ends with the block at `Y` holding the machine's zero matrix (`NLAlib.FloatMachine.zeroMat`),
every cell outside it unchanged, the same store shape and the same tape positions. No printed
source. -/
theorem holds_of_exec_zzero (p : P) (m n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st st' : St P K C}
    (h : exec I (zzero (ι := ι) p (.const m) (.const n) Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).zeroMat (Fin m) (Fin n)) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  have hrun : (zzero (ι := ι) p (.const m) (.const n) Y yo).run = .seq (.named "zzero"
      [.idx (.const m), .idx (.const n), .buf Y, .idx yo]
      (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.instr (.lit p ⟨Y, yo + .var w⟩ 0)) .skip) .skip)) .skip := rfl
  rw [hrun, exec_seq_skip, exec_named, exec_seq_skip] at h
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I
    (fun w s => s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
      (∀ k < w, s.store.read p Y (yo.eval + k) = some M.zero) ∧
      ∀ q b i, (b ≠ Y ∨ i < yo.eval ∨ yo.eval + w ≤ i) →
        s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h)
  · obtain ⟨hsh, hpos, hY, hfr⟩ := hR
    simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hY hfr
    refine ⟨fun i j t => ?_, fun q b i hb => hfr q b i ?_, hsh, hpos⟩
    · have hj := Nat.mul_le_mul_left m (show j.1 + 1 ≤ n from j.2)
      obtain ⟨t, ht⟩ := t
      change t < 2 at ht
      rw [Nat.mul_succ] at hj
      have hk : 2 * (i.1 + m * j.1) + t < 2 * (m * n) := by omega
      refine (hY _ hk).trans ?_
      rcases t with _ | _ | t
      · rfl
      · rfl
      · omega
    · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hb
      by_cases hbY : b = Y
      · exact Or.inr (by omega)
      · exact Or.inl hbY
  rintro w hw s₁ s₂ ⟨hsh, hpos, hY, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  simp only [IExp.eval_add, IExp.eval_var] at hw'
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hpos, fun k hk => ?_,
    fun q b i hb => (Store.read_of_write_eq_some_of_ne hw' ?_).trans (hfr q b i ?_)⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact (Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega))).trans (hY k hk)
    · refine (Store.read_of_write_eq_some hw').trans ?_
      have hv' : I.sem.lit p 0 = some v := by exact_mod_cast hv
      simp only [M, ScalarSem.toFloatMachine, hv', Option.getD_some]
  · by_cases hbY : b = Y
    · exact Or.inr (by omega)
    · exact Or.inl hbY
  · omega

omit [Inhabited K] in
/-- `zzero` succeeds under the standard model with every value in range, when the buffer `Y`
at tag `p` is long enough. No printed source. -/
theorem exists_exec_zzero (p : P) (m n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st : St P K C}
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (m * n) ≤ len) :
    ∃ st', exec I (zzero (ι := ι) p (.const m) (.const n) Y yo).run st = some st' := by
  obtain ⟨len, hYs, hlen⟩ := hY
  obtain ⟨z, hz⟩ := hsem.lit_ok p 0 trivial
  have hrun : (zzero (ι := ι) p (.const m) (.const n) Y yo).run = .seq (.named "zzero"
      [.idx (.const m), .idx (.const n), .buf Y, .idx yo]
      (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.instr (.lit p ⟨Y, yo + .var w⟩ 0)) .skip) .skip)) .skip := rfl
  rw [hrun, exec_seq_skip, exec_named, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I (fun _ s => s.store.shape = st.store.shape)
    rfl ?_).imp fun _ h => h.1
  rintro w hw s hsh
  simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hw
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape z (hsh ▸ hYs)
    (i := yo.eval + w) (by omega)
  exact ⟨_, (exec_seq_instr_lit I (by exact_mod_cast hz) hs').trans (exec_skip I _),
    (Store.shape_of_write_eq_some hs').trans hsh⟩

/-! ### Negation and the Hermitian completion -/

/-- `zneg` negates: a successful run of `NLAlib.Computation.zneg` from a state whose block at
`X` holds $\mathbf{A}$, into a block at `Y` disjoint from it or equal to it (in place), ends with
the block at `Y` holding the machine's negation of $\mathbf{A}$ (`NLAlib.FloatMachine.negMat`),
every cell outside it unchanged, the same store shape and the same tape positions. No printed
source. -/
theorem holds_of_exec_zneg (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {st st' : St P K C}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Y = X ∧ yo.eval = xo.eval))
    (h : exec I (zneg (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).negMat A) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  have hrun : (zneg (ι := ι) p (.const m) (.const n) X xo Y yo).run = .seq (.named "zneg"
      [.idx (.const m), .idx (.const n), .buf X, .idx xo, .buf Y, .idx yo]
      (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.instr (.un p .neg ⟨Y, yo + .var w⟩ ⟨X, xo + .var w⟩)) .skip) .skip)) .skip := rfl
  rw [hrun, exec_seq_skip, exec_named, exec_seq_skip] at h
  have hXw : ∀ w < 2 * (m * n), X ≠ Y ∨ xo.eval + w < yo.eval ∨ yo.eval + w ≤ xo.eval + w := by
    intro w hw
    rcases hXY with hXY | ⟨rfl, he⟩
    · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hXY
      by_cases hb : X = Y
      · exact Or.inr (by omega)
      · exact Or.inl hb
    · exact Or.inr (by omega)
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I
    (fun w s => s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
      (∀ k < w, s.store.read p Y (yo.eval + k) = (st.store.read p X (xo.eval + k)).map M.neg) ∧
      ∀ q b i, (b ≠ Y ∨ i < yo.eval ∨ yo.eval + w ≤ i) →
        s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h)
  · obtain ⟨hsh, hpos, hY, hfr⟩ := hR
    simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hY hfr
    refine ⟨fun i j t => ?_, fun q b i hb => hfr q b i ?_, hsh, hpos⟩
    · have hj := Nat.mul_le_mul_left m (show j.1 + 1 ≤ n from j.2)
      have ht : t.1 < 2 := t.2
      rw [Nat.mul_succ] at hj
      have hk : 2 * (i.1 + m * j.1) + t.1 < 2 * (m * n) := by omega
      refine (hY _ hk).trans ?_
      rw [show st.store.read p X (xo.eval + (2 * (i.1 + m * j.1) + t.1)) = _ from hA i j t,
        Option.map_some]
      obtain ⟨t, ht⟩ := t
      change t < 2 at ht
      rcases t with _ | _ | t
      · rfl
      · rfl
      · omega
    · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hb
      by_cases hbY : b = Y
      · exact Or.inr (by omega)
      · exact Or.inl hbY
  rintro w hw s₁ s₂ ⟨hsh, hpos, hY, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨a, ha, v, hv, s', hw', rfl⟩, rfl⟩ := hex
  simp only [IExp.eval_add, IExp.eval_var] at ha hw'
  simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hw
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hpos, fun k hk => ?_,
    fun q b i hb => (Store.read_of_write_eq_some_of_ne hw' ?_).trans (hfr q b i ?_)⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact (Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega))).trans (hY k hk)
    · rw [Store.read_of_write_eq_some hw', ← hfr _ _ _ (hXw k hw), ha, Option.map_some]
      simp only [M, ScalarSem.toFloatMachine, hv, Option.getD_some]
  · by_cases hbY : b = Y
    · exact Or.inr (by omega)
    · exact Or.inl hbY
  · omega

omit [Inhabited K] in
/-- `zneg` succeeds under the standard model with every value in range, when the buffer `Y` at
tag `p` is long enough. No printed source. -/
theorem exists_exec_zneg (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {st : St P K C}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Y = X ∧ yo.eval = xo.eval))
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (m * n) ≤ len) :
    ∃ st', exec I (zneg (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st' := by
  obtain ⟨len, hYs, hlen⟩ := hY
  have hX : ∀ k < 2 * (m * n), ∃ v, st.store.read p X (xo.eval + k) = some v := by
    intro k hk
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
    have e : 2 * (k / 2 % m + m * (k / 2 / m)) + k % 2 = k := by rw [Nat.mod_add_div]; omega
    exact ⟨_, e ▸ hA ⟨_, Nat.mod_lt _ hm⟩ ⟨_, Nat.div_lt_of_lt_mul (by omega)⟩
      ⟨_, Nat.mod_lt _ two_pos⟩⟩
  have hrun : (zneg (ι := ι) p (.const m) (.const n) X xo Y yo).run = .seq (.named "zneg"
      [.idx (.const m), .idx (.const n), .buf X, .idx xo, .buf Y, .idx yo]
      (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.instr (.un p .neg ⟨Y, yo + .var w⟩ ⟨X, xo + .var w⟩)) .skip) .skip)) .skip := rfl
  rw [hrun, exec_seq_skip, exec_named, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I
    (fun w s => s.store.shape = st.store.shape ∧ ∀ k < 2 * (m * n), w ≤ k →
      s.store.read p X (xo.eval + k) = st.store.read p X (xo.eval + k))
    ⟨rfl, fun _ _ _ => rfl⟩ ?_).imp fun _ h => h.1
  rintro w hw s ⟨hsh, hs⟩
  simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hw
  obtain ⟨v, hv⟩ := hX w hw
  obtain ⟨z, hz, -⟩ := hsem.neg p v
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape z (hsh ▸ hYs)
    (i := yo.eval + w) (by omega)
  refine ⟨_, (exec_seq_instr_un I (by exact (hs w hw le_rfl).trans hv) hz hs').trans
    (exec_skip I _), (Store.shape_of_write_eq_some hs').trans hsh, fun k hk hwk => ?_⟩
  refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans (hs k hk (by omega))
  rcases hXY with hXY | ⟨rfl, he⟩
  · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hXY
    by_cases hb : X = Y
    · exact Or.inr (by omega)
    · exact Or.inl hb
  · exact Or.inr (by omega)

omit [Inhabited K] in
private theorem zmirror_holds_hermFrom {Su Sg : Type} {p : P} {n Y off : ℕ} {s s' : Store P K}
    {B : Matrix (Fin n) (Fin n) (K × K)} (M : FloatMachine K Su Sg)
    (hB : ∀ i j : Fin n, i ≤ j → s.read p Y (off + 2 * (i + n * j)) = some (B i j).1 ∧
      s.read p Y (off + 2 * (i + n * j) + 1) = some (B i j).2)
    (hdiag : ∀ i, (B i i).2 = M.zero)
    (hw : ∀ a b : Fin n, b < a → s'.read p Y (off + 2 * (a + n * b)) = some (B b a).1 ∧
      s'.read p Y (off + 2 * (a + n * b) + 1) = some (M.neg (B b a).2))
    (hfr : ∀ q c k, (c ≠ Y ∨ ∀ a b : Fin n, b < a →
      k ≠ off + 2 * (a + n * b) ∧ k ≠ off + 2 * (a + n * b) + 1) → s'.read q c k = s.read q c k) :
    pairLayout.Holds s' p Y off (M.hermFrom (fun i j => B i j) fun i => (B i i).1) ∧
      ∀ q c k, blockDisjoint (c, k, 1) (Y, off, 2 * (n * n)) = true →
        s'.read q c k = s.read q c k := by
  have hU : ∀ (a b : Fin n) (t : ℕ), a ≤ b → t < 2 →
      s'.read p Y (off + (2 * (a + n * b) + t)) = s.read p Y (off + (2 * (a + n * b) + t)) := by
    intro a b t hab ht
    refine hfr _ _ _ (Or.inr fun a' b' hab' => ?_)
    have h1 : a.1 ≤ b.1 := hab
    have h2 : b'.1 < a'.1 := hab'
    constructor <;> intro he
    · have := (Nat.add_mul_eq_add_mul_iff_of_lt a.2 a'.2).1
        (show a.1 + n * b = a' + n * b' by omega)
      omega
    · have := (Nat.add_mul_eq_add_mul_iff_of_lt a.2 a'.2).1
        (show a.1 + n * b = a' + n * b' by omega)
      omega
  refine ⟨fun a b t => ?_, fun q c k hk => hfr q c k ?_⟩
  · obtain ⟨t, ht⟩ := t
    change t < 2 at ht
    change s'.read p Y (off + (2 * (a.1 + n * b.1) + t)) = some (pairLayout.put _ _)
    rcases lt_trichotomy a b with hab | rfl | hab
    · rw [hU a b t hab.le ht]
      simp only [FloatMachine.hermFrom, Matrix.of_apply, if_pos hab]
      rcases t with _ | _ | t
      exacts [(hB a b hab.le).1, (hB a b hab.le).2, by omega]
    · rw [hU a a t le_rfl ht]
      simp only [FloatMachine.hermFrom, Matrix.of_apply, lt_irrefl, if_false]
      rcases t with _ | _ | t
      exacts [(hB a a le_rfl).1, (hB a a le_rfl).2.trans (congrArg some (hdiag a)), by omega]
    · simp only [FloatMachine.hermFrom, Matrix.of_apply, if_neg (not_lt.mpr hab.le), if_pos hab]
      rcases t with _ | _ | t
      exacts [(hw a b hab).1, (hw a b hab).2, by omega]
  · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hk
    by_cases hc : c = Y
    · refine Or.inr fun a b _ => ?_
      have hb := Nat.mul_le_mul_left n (show b.1 + 1 ≤ n from b.2)
      have ha := a.2
      rw [Nat.mul_succ] at hb
      omega
    · exact Or.inl hc

omit [Inhabited K] in
private theorem zmirror_step {n Y i j : ℕ} {p : P} {yo : IExp ℕ} {st s₁ s₂ : St P K C}
    {B : Matrix (Fin n) (Fin n) (K × K)} (M : FloatMachine K Su Sg)
    (hneg : ∀ x z, I.sem.un p .neg x = some z → M.neg x = z)
    (hB : ∀ i j : Fin n, i ≤ j → st.store.read p Y (yo.eval + 2 * (i + n * j)) = some (B i j).1 ∧
      st.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some (B i j).2)
    (hi : i < (IExp.var j).eval) (hj : j < n)
    (hR : s₁.store.shape = st.store.shape ∧ s₁.pos = st.pos ∧
      (∀ a b : Fin n, b < a → (a.1 < j ∨ a.1 = j ∧ b.1 < i) →
        s₁.store.read p Y (yo.eval + 2 * (a + n * b)) = some (B b a).1 ∧
        s₁.store.read p Y (yo.eval + 2 * (a + n * b) + 1) = some (M.neg (B b a).2)) ∧
      ∀ q c k, (c ≠ Y ∨ ∀ a b : Fin n, b < a → (a.1 < j ∨ a.1 = j ∧ b.1 < i) →
        k ≠ yo.eval + 2 * (a + n * b) ∧ k ≠ yo.eval + 2 * (a + n * b) + 1) →
        s₁.store.read q c k = st.store.read q c k)
    (hex : exec I (.seq (.instr (.copy p ⟨Y, yo + zidx (.const n) (.var j) (.var i)⟩
      ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩))
      (.seq (.instr (.un p .neg ⟨Y, yo + zidx (.const n) (.var j) (.var i) + 1⟩
        ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩)) .skip)) s₁ = some s₂) :
    s₂.store.shape = st.store.shape ∧ s₂.pos = st.pos ∧
      (∀ a b : Fin n, b < a → (a.1 < j ∨ a.1 = j ∧ b.1 < i + 1) →
        s₂.store.read p Y (yo.eval + 2 * (a + n * b)) = some (B b a).1 ∧
        s₂.store.read p Y (yo.eval + 2 * (a + n * b) + 1) = some (M.neg (B b a).2)) ∧
      ∀ q c k, (c ≠ Y ∨ ∀ a b : Fin n, b < a → (a.1 < j ∨ a.1 = j ∧ b.1 < i + 1) →
        k ≠ yo.eval + 2 * (a + n * b) ∧ k ≠ yo.eval + 2 * (a + n * b) + 1) →
        s₂.store.read q c k = st.store.read q c k := by
  obtain ⟨sh, ps, hw, hfr⟩ := hR
  simp only [IExp.eval_var] at hi
  simp only [exec_seq, exec_instr, exec_skip, Instr.run, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
    IExp.eval_ofNat] at hex
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw1, rfl⟩, rfl⟩, _, ⟨_, ⟨u, hu, z, hz, s'', hw2, rfl⟩, rfl⟩, hs₂⟩ :=
    hex
  obtain rfl := Option.some_inj.mp hs₂
  have hi' : i < n := by omega
  have hU : ∀ t < 2, s₁.store.read p Y (yo.eval + 2 * (i + n * j) + t) =
      st.store.read p Y (yo.eval + 2 * (i + n * j) + t) := by
    intro t ht
    refine hfr _ _ _ (Or.inr fun a b hab _ => ?_)
    have hab' : b.1 < a.1 := hab
    constructor <;> intro he
    · have := (Nat.add_mul_eq_add_mul_iff_of_lt hi' a.2).1 (show i + n * j = a + n * b by omega)
      omega
    · have := (Nat.add_mul_eq_add_mul_iff_of_lt hi' a.2).1 (show i + n * j = a + n * b by omega)
      omega
  obtain ⟨hB1, hB2⟩ := hB ⟨i, hi'⟩ ⟨j, hj⟩ (Fin.mk_le_mk.mpr hi.le)
  obtain rfl : v = (B ⟨i, hi'⟩ ⟨j, hj⟩).1 :=
    Option.some_inj.mp (hv.symm.trans ((hU 0 (by omega)).trans hB1))
  obtain rfl : u = (B ⟨i, hi'⟩ ⟨j, hj⟩).2 := Option.some_inj.mp
    (((Store.read_of_write_eq_some_of_ne hw1 (Or.inr (by omega))).symm.trans hu).symm.trans
      ((hU 1 (by omega)).trans hB2))
  have hz' := hneg _ _ hz
  refine ⟨(Store.shape_of_write_eq_some hw2).trans ((Store.shape_of_write_eq_some hw1).trans sh),
    ps, fun a b hab hd => ?_, fun q c k hk => ?_⟩
  · have hab' : b.1 < a.1 := hab
    by_cases hab'' : a.1 = j ∧ b.1 = i
    · obtain ⟨ha, hb⟩ := hab''
      obtain rfl : a = ⟨j, hj⟩ := Fin.ext ha
      obtain rfl : b = ⟨i, hi'⟩ := Fin.ext hb
      refine ⟨?_, ?_⟩
      · rw [Store.read_of_write_eq_some_of_ne hw2 (Or.inr (by omega)),
          Store.read_of_write_eq_some hw1]
      · rw [Store.read_of_write_eq_some hw2, hz']
    · have hd' : a.1 < j ∨ (a.1 = j ∧ b.1 < i) := by omega
      have hne : ∀ t < 2, ∀ t' < 2, yo.eval + 2 * (a + n * b) + t ≠
          yo.eval + 2 * (j + n * i) + t' := by
        intro t ht t' ht' he
        have := (Nat.add_mul_eq_add_mul_iff_of_lt a.2 hj).1 (show a.1 + n * b = j + n * i by omega)
        omega
      exact ⟨(Store.read_of_write_eq_some_of_ne hw2 (Or.inr (hne 0 (by omega) 1 (by omega)))).trans
        ((Store.read_of_write_eq_some_of_ne hw1 (Or.inr (hne 0 (by omega) 0 (by omega)))).trans
          (hw a b hab hd').1),
        (Store.read_of_write_eq_some_of_ne hw2 (Or.inr (hne 1 (by omega) 1 (by omega)))).trans
        ((Store.read_of_write_eq_some_of_ne hw1 (Or.inr (hne 1 (by omega) 0 (by omega)))).trans
          (hw a b hab hd').2)⟩
  · have hk' : c ≠ Y ∨ (k ≠ yo.eval + 2 * (j + n * i) ∧ k ≠ yo.eval + 2 * (j + n * i) + 1) :=
      hk.imp_right fun H => H ⟨j, hj⟩ ⟨i, hi'⟩ hi (Or.inr ⟨rfl, Nat.lt_succ_self _⟩)
    rw [Store.read_of_write_eq_some_of_ne hw2 (hk'.imp_right And.right),
      Store.read_of_write_eq_some_of_ne hw1 (hk'.imp_right And.left)]
    exact hfr q c k (hk.imp_right fun H a b hab hd => H a b hab (by omega))

/-- `zmirror` completes a stored Hermitian matrix: if the block at `Y` holds the parts of the
entries $b_{ij}$, $i \le j$, of a complex $n \times n$ matrix $\mathbf{B}$ whose diagonal
imaginary parts are the machine's zero, a successful run of `NLAlib.Computation.zmirror` ends
with the block holding the machine's Hermitian matrix with upper triangle and real diagonal those
of $\mathbf{B}$ (`NLAlib.FloatMachine.hermFrom`), every cell outside it unchanged, the same store
shape and the same tape positions. No printed source. -/
theorem holds_of_exec_zmirror (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st st' : St P K C}
    {B : Matrix (Fin n) (Fin n) (K × K)}
    (hB : ∀ i j : Fin n, i ≤ j → st.store.read p Y (yo.eval + 2 * (i + n * j)) = some (B i j).1 ∧
      st.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some (B i j).2)
    (hdiag : ∀ i, (B i i).2 = (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero)
    (h : exec I (zmirror (ι := ι) p (.const n) Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermFrom (fun i j => B i j)
        fun i => (B i i).1) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  have hprog : (zmirror (ι := ι) p (.const n) Y yo).run = .seq (.named "zmirror"
      [.idx (.const n), .buf Y, .idx yo] (.seq (.loop (.const n) fun j =>
        .seq (.loop (.var j) fun i =>
          .seq (.instr (.copy p ⟨Y, yo + zidx (.const n) (.var j) (.var i)⟩
            ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩))
          (.seq (.instr (.un p .neg ⟨Y, yo + zidx (.const n) (.var j) (.var i) + 1⟩
            ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩)) .skip)) .skip) .skip)) .skip := rfl
  rw [hprog, exec_seq_skip, exec_named, exec_seq_skip] at h
  let Inv : (ℕ → ℕ → Prop) → St P K C → Prop := fun d s =>
    s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
    (∀ a b : Fin n, b < a → d a b →
      s.store.read p Y (yo.eval + 2 * (a + n * b)) = some (B b a).1 ∧
      s.store.read p Y (yo.eval + 2 * (a + n * b) + 1) = some (M.neg (B b a).2)) ∧
    ∀ q c k, (c ≠ Y ∨ ∀ a b : Fin n, b < a → d a b →
      k ≠ yo.eval + 2 * (a + n * b) ∧ k ≠ yo.eval + 2 * (a + n * b) + 1) →
      s.store.read q c k = st.store.read q c k
  have hconv : ∀ (d d' : ℕ → ℕ → Prop) s, (∀ a b : Fin n, b < a → (d a b ↔ d' a b)) →
      Inv d s → Inv d' s := by
    rintro d d' s H ⟨sh, ps, hw, hfr⟩
    exact ⟨sh, ps, fun a b hab hd => hw a b hab ((H a b hab).2 hd), fun q c k hk =>
      hfr q c k (hk.imp_right fun H' a b hab hd => H' a b hab ((H a b hab).1 hd))⟩
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I (fun j s => Inv (fun a _ => a < j) s)
    ⟨rfl, rfl, fun _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h)
  · obtain ⟨sh, ps, hw, hfr⟩ := hR
    obtain ⟨h1, h2⟩ := zmirror_holds_hermFrom M hB hdiag (fun a b hab => hw a b hab a.2)
      fun q c k hk => hfr q c k (hk.imp_right fun H a b hab _ => H a b hab)
    exact ⟨h1, h2, sh, ps⟩
  rintro j hj s₁ s₂ hR₁ hex
  simp only [IExp.eval_const] at hj
  rw [exec_seq_skip] at hex
  refine hconv (fun a b => a < j ∨ (a = j ∧ b < (IExp.var j).eval)) (fun a _ => a < j + 1) s₂
    (fun a b hab => ?_) (forall_of_exec_loop_eq_some I
    (fun i s => Inv (fun a b => a < j ∨ (a = j ∧ b < i)) s)
    (hconv (fun a _ => a < j) (fun a b => a < j ∨ (a = j ∧ b < 0)) s₁
      (fun a b _ => ⟨Or.inl, fun h => h.elim id fun h => absurd h.2 (Nat.not_lt_zero _)⟩) hR₁)
    ?_ hex)
  · simp only [IExp.eval_var]
    omega
  rintro i hi s₁ s₂ hR hex
  exact zmirror_step M (fun x z hz => by simp only [M, ScalarSem.toFloatMachine, hz,
    Option.getD_some]) hB hi hj hR hex

omit [Inhabited K] in
/-- `zmirror` succeeds under the standard model with every value in range, when the block at
`Y` holds the upper triangle of $\mathbf{B}$ and the buffer `Y` at tag `p` is long enough. No
printed source. -/
theorem exists_exec_zmirror (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st : St P K C}
    {B : Matrix (Fin n) (Fin n) (K × K)}
    (hB : ∀ i j : Fin n, i < j → st.store.read p Y (yo.eval + 2 * (i + n * j)) = some (B i j).1 ∧
      st.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some (B i j).2)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zmirror (ι := ι) p (.const n) Y yo).run st = some st' := by
  obtain ⟨len, hYs, hlen⟩ := hY
  have hn : ∀ i j : ℕ, i < n → j < n → 2 * (i + n * j) + 1 < 2 * (n * n) := by
    intro i j hi hj; nlinarith
  have hprog : (zmirror (ι := ι) p (.const n) Y yo).run = .seq (.named "zmirror"
      [.idx (.const n), .buf Y, .idx yo] (.seq (.loop (.const n) fun j =>
        .seq (.loop (.var j) fun i =>
          .seq (.instr (.copy p ⟨Y, yo + zidx (.const n) (.var j) (.var i)⟩
            ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩))
          (.seq (.instr (.un p .neg ⟨Y, yo + zidx (.const n) (.var j) (.var i) + 1⟩
            ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩)) .skip)) .skip) .skip)) .skip := rfl
  rw [hprog, exec_seq_skip, exec_named, exec_seq_skip]
  let R : St P K C → Prop := fun s => s.store.shape = st.store.shape ∧ ∀ i j : Fin n, i < j →
    s.store.read p Y (yo.eval + 2 * (i + n * j)) = st.store.read p Y (yo.eval + 2 * (i + n * j)) ∧
    s.store.read p Y (yo.eval + 2 * (i + n * j) + 1) =
      st.store.read p Y (yo.eval + 2 * (i + n * j) + 1)
  refine (exists_exec_loop_eq_some_of_forall I (fun _ s => R s)
    ⟨rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩ ?_).imp fun _ h => h.1
  rintro j hj s₁ hR₁
  simp only [IExp.eval_const] at hj
  rw [exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall I (fun _ s => R s) hR₁ ?_
  rintro i hi s ⟨hsh, hs⟩
  simp only [IExp.eval_var] at hi
  have hi' : i < n := by omega
  obtain ⟨hb1, hb2⟩ := hB ⟨i, hi'⟩ ⟨j, hj⟩ (Fin.mk_lt_mk.mpr hi)
  obtain ⟨e1, e2⟩ := hs ⟨i, hi'⟩ ⟨j, hj⟩ (Fin.mk_lt_mk.mpr hi)
  have hne : ∀ a b : Fin n, a < b → ∀ t < 2, ∀ t' < 2,
      yo.eval + 2 * (a + n * b) + t ≠ yo.eval + 2 * (j + n * i) + t' := by
    intro a b hab t ht t' ht' he
    have hab' : a.1 < b.1 := hab
    have := (Nat.add_mul_eq_add_mul_iff_of_lt a.2 hj).1 (show a.1 + n * b = j + n * i by omega)
    omega
  have hk := hn j i hj hi'
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape (B ⟨i, hi'⟩ ⟨j, hj⟩).1
    (hsh ▸ hYs) (i := yo.eval + 2 * (j + n * i)) (by omega)
  obtain ⟨z, hz, -⟩ := hsem.neg p (B ⟨i, hi'⟩ ⟨j, hj⟩).2
  have hsh' := (Store.shape_of_write_eq_some hs').trans hsh
  obtain ⟨s'', hs''⟩ := Store.exists_write_eq_some_of_getElem?_shape z
    (hsh' ▸ hYs) (i := yo.eval + 2 * (j + n * i) + 1) (by omega)
  have hidx : ∀ a b : ℕ,
      (yo + zidx (.const n) (.var a) (.var b)).eval = yo.eval + 2 * (a + n * b) := by
    intro a b; simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
      IExp.eval_ofNat]
  have hidx1 : ∀ a b : ℕ, (yo + zidx (.const n) (.var a) (.var b) + 1).eval =
      yo.eval + 2 * (a + n * b) + 1 := by
    intro a b; simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
      IExp.eval_ofNat]
  have r1 : s.store.read p Y (yo + zidx (.const n) (.var i) (.var j)).eval =
      some (B ⟨i, hi'⟩ ⟨j, hj⟩).1 := by rw [hidx, e1, hb1]
  have w1 : s.store.write p Y (yo + zidx (.const n) (.var j) (.var i)).eval
      (B ⟨i, hi'⟩ ⟨j, hj⟩).1 = some s' := by rw [hidx]; exact hs'
  have r2 : s'.read p Y (yo + zidx (.const n) (.var i) (.var j) + 1).eval =
      some (B ⟨i, hi'⟩ ⟨j, hj⟩).2 := by
    rw [hidx1, Store.read_of_write_eq_some_of_ne hs' (Or.inr (by omega)), e2, hb2]
  have w2 : s'.write p Y (yo + zidx (.const n) (.var j) (.var i) + 1).eval z = some s'' := by
    rw [hidx1]; exact hs''
  refine ⟨_, (exec_seq_instr_copy I (dst := ⟨Y, _⟩) (src := ⟨Y, _⟩) r1 w1).trans
    ((exec_seq_instr_un I (dst := ⟨Y, _⟩) (x := ⟨Y, _⟩) r2 hz w2).trans (exec_skip I _)), ?_,
    fun a b hab => ?_⟩
  · exact (Store.shape_of_write_eq_some hs'').trans hsh'
  · obtain ⟨f1, f2⟩ := hs a b hab
    have h00 := hne a b hab 0 (by omega) 0 (by omega)
    have h01 := hne a b hab 0 (by omega) 1 (by omega)
    have h10 := hne a b hab 1 (by omega) 0 (by omega)
    have h11 := hne a b hab 1 (by omega) 1 (by omega)
    simp only [add_zero] at h00 h01 h10 h11
    exact ⟨by rw [Store.read_of_write_eq_some_of_ne hs'' (Or.inr h01),
        Store.read_of_write_eq_some_of_ne hs' (Or.inr h00), f1],
      by rw [Store.read_of_write_eq_some_of_ne hs'' (Or.inr h11),
        Store.read_of_write_eq_some_of_ne hs' (Or.inr h10), f2]⟩

end NLAlib.Computation
