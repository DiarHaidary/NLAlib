/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlib.Computation.BLAS
public import NLAlib.Matrix.Computation.EntrywiseRounding
public import NLAlib.Matrix.Computation.InterpMachine
public import NLAlibScaffold.Computation.Exec

/-!
# The complex-pair kernels compute the floating-point machine's operations (scaffold)

Statements for a new file `NLAlib/Matrix/Computation/PairKernels.lean` (stage COMPDYN S1c,
design note `docs/design/Computation-SignDeflatePrograms.md`, §2): the **rounded
specifications** of the complex kernels of `NLAlib/Computation/BLAS.lean`. Under any
interpretation, a successful run of a kernel on blocks that hold stored complex matrices
(`NLAlib.Computation.EntryLayout.Holds`, interleaved layout) ends with the output block holding
exactly the result of the corresponding operation of the machine of the semantics
(`NLAlib.Computation.ScalarSem.toFloatMachine`), one rounding per real operation, and every other
cell unchanged; and the run succeeds when the operations it performs succeed. With the exact
specifications of `NLAlib/Matrix/Computation/InterpMachine.lean` (scaffold) and the machine
contract, these give the exact and the rounded behaviour of each kernel.

## Main results

* `NLAlib.Computation.holds_of_exec_zcopy`, `NLAlib.Computation.holds_of_exec_zzero`,
  `NLAlib.Computation.holds_of_exec_zneg`, `NLAlib.Computation.holds_of_exec_zmirror`,
  `NLAlib.Computation.holds_of_exec_zhermShift`, `NLAlib.Computation.holds_of_exec_zhermScale`,
  `NLAlib.Computation.holds_of_exec_zhermAvg`, `NLAlib.Computation.read_of_exec_zboxTest`, and
  for the kernels SIGN and DEFLATE do not call, `NLAlib.Computation.holds_of_exec_zidentity`,
  `NLAlib.Computation.holds_of_exec_zadd`, `NLAlib.Computation.holds_of_exec_zsub`,
  `NLAlib.Computation.holds_of_exec_zscal`, `NLAlib.Computation.holds_of_exec_zconjTranspose`,
  `NLAlib.Computation.read_of_exec_ztraceRe`: what a successful run computes.
* `NLAlib.Computation.exists_exec_zcopy`, `NLAlib.Computation.exists_exec_zzero`,
  `NLAlib.Computation.exists_exec_zneg`, `NLAlib.Computation.exists_exec_zmirror`,
  `NLAlib.Computation.exists_exec_zhermShift`, `NLAlib.Computation.exists_exec_zhermScale`,
  `NLAlib.Computation.exists_exec_zhermAvg`, `NLAlib.Computation.exists_exec_zboxTest`: when the
  run succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### Copies and literals -/

/-- **`zcopy` copies**: a successful run of `NLAlib.Computation.zcopy` from a state whose block at
`X` holds the complex $m \times n$ matrix $\mathbf{A}$, into a block at `Y` disjoint from it,
ends with the block at `Y` holding $\mathbf{A}$, every cell outside it unchanged, the same store
shape and the same tape positions. No printed source.
Proof: `NLAlib.Computation.forall_of_exec_loop_eq_some` (scaffold) on the word loop with the
invariant "words below $w$ copied, the rest unchanged"; each step is
`NLAlib.Computation.exec_seq_instr_copy` with `NLAlib.Computation.Store.read_of_write_eq_some`
and `NLAlib.Computation.Store.read_of_write_eq_some_of_ne`; then
`NLAlib.Computation.pairLayout.holds_iff` (scaffold). M, about 40 lines. -/
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

/-- **`zcopy` succeeds** from a state whose block at `X` holds a complex $m \times n$ matrix and
whose buffer `Y` at tag `p` is long enough. No printed source.
Proof: `NLAlib.Computation.exists_exec_loop_eq_some_of_forall` with the invariant "the store has
the shape of `st` and the block at `X` still holds $\mathbf{A}$" (disjointness);
`NLAlib.Computation.Store.exists_write_eq_some_of_getElem?_shape`. S, about 20 lines. -/
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

/-- **`zzero` writes the stored zero matrix**: a successful run of `NLAlib.Computation.zzero`
ends with the block at `Y` holding the machine's zero matrix (`NLAlib.FloatMachine.zeroMat`),
every cell outside it unchanged, the same store shape and the same tape positions. No printed
source.
Proof: as `NLAlib.Computation.holds_of_exec_zcopy`, each step
`NLAlib.Computation.exec_seq_instr_lit`; the literal $0$ read off its successful run is the
machine's zero (`Option.getD_some`). M, about 30 lines. -/
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

/-- **`zzero` succeeds** under the standard model with every value in range, when the buffer `Y`
at tag `p` is long enough. No printed source.
Proof: as `NLAlib.Computation.exists_exec_zcopy`, each literal by `lit_ok` (`trivial`). S, about
15 lines. -/
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

/-- **`zneg` negates**: a successful run of `NLAlib.Computation.zneg` from a state whose block at
`X` holds $\mathbf{A}$, into a block at `Y` disjoint from it or equal to it (in place), ends with
the block at `Y` holding the machine's negation of $\mathbf{A}$ (`NLAlib.FloatMachine.negMat`),
every cell outside it unchanged, the same store shape and the same tape positions. No printed
source.
Proof: as `NLAlib.Computation.holds_of_exec_zcopy`; in place, word $w$ is read before it is
written and never read again. M, about 40 lines. -/
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

/-- **`zneg` succeeds** under the standard model with every value in range, when the buffer `Y` at
tag `p` is long enough. No printed source.
Proof: as `NLAlib.Computation.exists_exec_zcopy`, each negation by the `neg` clause. S, about 20
lines. -/
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

private theorem zmirror_index_inj {n a b a' b' : ℕ} (ha : a < n) (ha' : a' < n)
    (he : a + n * b = a' + n * b') : a = a' ∧ b = b' := by
  have hn : 0 < n := by omega
  have h1 := congrArg (· % n) he
  have h2 := congrArg (· / n) he
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h1
  simp only [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt ha',
    zero_add] at h2
  exact ⟨h1, h2⟩

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
    · have := zmirror_index_inj a.2 a'.2 (show a.1 + n * b = a' + n * b' by omega)
      omega
    · have := zmirror_index_inj a.2 a'.2 (show a.1 + n * b = a' + n * b' by omega)
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
    · have := zmirror_index_inj hi' a.2 (show i + n * j = a + n * b by omega)
      omega
    · have := zmirror_index_inj hi' a.2 (show i + n * j = a + n * b by omega)
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
        have := zmirror_index_inj a.2 hj (show a.1 + n * b = j + n * i by omega)
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

/-- **`zmirror` completes a stored Hermitian matrix**: if the block at `Y` holds the parts of the
entries $b_{ij}$, $i \le j$, of a complex $n \times n$ matrix $\mathbf{B}$ whose diagonal
imaginary parts are the machine's zero, a successful run of `NLAlib.Computation.zmirror` ends
with the block holding the machine's Hermitian matrix with upper triangle and real diagonal those
of $\mathbf{B}$ (`NLAlib.FloatMachine.hermFrom`), every cell outside it unchanged, the same store
shape and the same tape positions. No printed source.
Proof: `NLAlib.Computation.forall_of_exec_loop_eq_some` (scaffold) twice, the invariant "the
upper triangle and the diagonal unchanged, the entries $(j', i)$ with $i < j'$, $j' < j$ written";
each step reads an upper entry (never written by the loop) and writes a lower one
(`NLAlib.Computation.exec_seq_instr_copy`, `NLAlib.Computation.exec_seq_instr_un`); the index
$2(j + ni)$ of a lower entry differs from every upper index (`omega` on `i < j`). M, about 60
lines. -/
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

/-- **`zmirror` succeeds** under the standard model with every value in range, when the block at
`Y` holds the upper triangle of $\mathbf{B}$ and the buffer `Y` at tag `p` is long enough. No
printed source.
Proof: as `NLAlib.Computation.exists_exec_zcopy`, with the invariant of
`NLAlib.Computation.holds_of_exec_zmirror`. S, about 25 lines. -/
theorem exists_exec_zmirror (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st : St P K C}
    {B : Matrix (Fin n) (Fin n) (K × K)}
    (hB : ∀ i j : Fin n, i < j → st.store.read p Y (yo.eval + 2 * (i + n * j)) = some (B i j).1 ∧
      st.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some (B i j).2)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zmirror (ι := ι) p (.const n) Y yo).run st = some st' := by
  sorry

/-! ### The Hermitian kernels -/

/-- **`zhermShift` computes the machine's shift**: a successful run of
`NLAlib.Computation.zhermShift` from a state whose block at `X` holds the complex $n \times n$
matrix $\mathbf{A}$ and whose cell `c` holds $c$, into a block at `Y` disjoint from the block at
`X` and from `c`, ends with the block at `Y` holding `M.hermShift A c` for the machine `M` of the
semantics at `p`, every cell outside it unchanged, the same store shape and the same tape
positions. No printed source.
Proof: the run is three statements in sequence (`NLAlib.Computation.exec_run_bind`): the upper
copy loop (as `NLAlib.Computation.holds_of_exec_zcopy`, on the entries $i < j$), the diagonal loop
(`NLAlib.Computation.exec_seq_instr_bin` with the sub's result, then the literal $0$), and
`NLAlib.Computation.holds_of_exec_zmirror` with $\mathbf{B}$ the upper copy and the diagonal; the
read-back values are the machine's (`Option.getD_some`), and `NLAlib.FloatMachine.hermShift`
unfolds to that `NLAlib.FloatMachine.hermFrom`. M, about 60 lines. -/
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
  sorry

/-- **`zhermShift` succeeds** under the standard model with every value in range, when the buffer
`Y` at tag `p` is long enough. No printed source.
Proof: `NLAlib.Computation.exists_exec_zcopy`-style loops for the copy and the diagonal, then
`NLAlib.Computation.exists_exec_zmirror`, the frames of the earlier loops giving its hypotheses;
each operation by `bin_ok`, `lit_ok`, `neg` (`trivial` for the range). M, about 40 lines. -/
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
  sorry

/-- **`zhermScale` computes the machine's scaling**: as
`NLAlib.Computation.holds_of_exec_zhermShift`, the block at `Y` ends holding `M.hermScale A c`.
No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zhermShift`, the upper loop dividing both parts.
M, about 60 lines. -/
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
  sorry

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

/-- **`zhermScale` succeeds** under the standard model with every value in range, when $c$ decodes
to a nonzero value and the buffer `Y` at tag `p` is long enough. No printed source.
Proof: as `NLAlib.Computation.exists_exec_zhermShift`, the divisions by `bin_ok` with `hcv`.
M, about 40 lines. -/
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

/-- **`zhermAvg` computes the machine's Hermitian part**: as
`NLAlib.Computation.holds_of_exec_zhermShift`, the block at `Y` ends holding `M.hermAvg A c`.
No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zhermShift`; each upper part is written twice (the
sum or difference, then its quotient), which `NLAlib.Computation.Store.write_of_write_eq_some`
collapses. M, about 70 lines. -/
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
  sorry

omit [DecidableEq P] [Inhabited K] in
private theorem zhermAvg_bind {α β : Type} {o : Option α} {f : α → Option β} (R : α → Prop)
    (h₁ : ∃ a, o = some a ∧ R a) (h₂ : ∀ a, R a → ∃ b, f a = some b) :
    ∃ b, o.bind f = some b := by
  obtain ⟨a, rfl, ha⟩ := h₁
  exact h₂ a ha

omit [DecidableEq P] in
private theorem zhermAvg_disj {X Y xo yo N k : ℕ}
    (h : blockDisjoint (Y, yo, N) (X, xo, N) = true) (hk : k < N) :
    blockDisjoint (X, xo + k, 1) (Y, yo, N) = true := by
  simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h ⊢
  omega

omit [Inhabited K] in
private theorem zhermAvg_write {s₀ s : Store P K} {p : P} {Y yo len k N : ℕ}
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
private theorem zhermAvg_bin {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) {p : P} {b : BinOp} (hb : b.IsArith)
    {st σ : St P K C} {Y yo len N : ℕ}
    (hYsh : st.store.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len)
    (hsh : σ.store.shape = st.store.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true →
      σ.store.read q b i = st.store.read q b i)
    (dk : IExp ℕ) (x y : Cell ℕ ℕ) (k : ℕ) (hk : k < N) (hdk : dk.eval = yo + k)
    (hx : ∃ a, σ.store.read p x.buf x.idx.eval = some a)
    (hy : ∃ c, σ.store.read p y.buf y.idx.eval = some c ∧ (b = .div → dec p c ≠ 0)) :
    ∃ s', (∀ t, exec I (.seq (.instr (.bin p b ⟨Y, dk⟩ x y)) t) σ =
        exec I t { σ with store := s', cnt := σ.cnt + I.charge (.bin p b) }) ∧
      s'.shape = st.store.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = st.store.read q b i) ∧
      (∃ w, s'.read p Y (yo + k) = some w) ∧
      ∀ k', (∃ w, σ.store.read p Y k' = some w) → ∃ w, s'.read p Y k' = some w := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨c, hc, hc0⟩ := hy
  obtain ⟨v, hv⟩ := hsem.bin_ok p b a c hb hc0 trivial
  obtain ⟨s', hw, hrest⟩ := zhermAvg_write hYsh hlen hk hsh hfr v
  exact ⟨s', fun t => exec_seq_instr_bin I ha hc hv (by rw [hdk]; exact hw), hrest⟩

omit [Inhabited K] in
private theorem zhermAvg_lit {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) {p : P} {st σ : St P K C}
    {Y yo len N : ℕ} (hYsh : st.store.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len)
    (hsh : σ.store.shape = st.store.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true →
      σ.store.read q b i = st.store.read q b i)
    (dk : IExp ℕ) (k : ℕ) (hk : k < N) (hdk : dk.eval = yo + k) :
    ∃ s', (∀ t, exec I (.seq (.instr (.lit p ⟨Y, dk⟩ 0)) t) σ =
        exec I t { σ with store := s', cnt := σ.cnt + I.charge (.lit p) }) ∧
      s'.shape = st.store.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = st.store.read q b i) ∧
      ∀ k', (∃ w, σ.store.read p Y k' = some w) → ∃ w, s'.read p Y k' = some w := by
  obtain ⟨v, hv⟩ := hsem.lit_ok p 0 trivial
  obtain ⟨s', hw, hsh', hfr', -, hmono⟩ := zhermAvg_write hYsh hlen hk hsh hfr v
  exact ⟨s', fun t => exec_seq_instr_lit I hv (by rw [hdk]; exact hw), hsh', hfr', hmono⟩

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
    ⟨⟨_, (hs _ _ _ (zhermAvg_disj hXY (by have := hn i j hi hj; omega))).trans
        (hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨0, Nat.zero_lt_two⟩)⟩,
      ⟨_, (hs _ _ _ (zhermAvg_disj hXY (hn i j hi hj))).trans
        (hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨1, Nat.one_lt_two⟩)⟩⟩
  have hC : ∀ s : Store P K, (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      s.read q b i = st.store.read q b i) →
      ∃ c', s.read p c.buf c.idx.eval = some c' ∧ (BinOp.div = .div → dec p c' ≠ 0) :=
    fun s hs => ⟨cv, (hs _ _ _ hcY).trans hc, fun _ => hcv⟩
  have hk := hn i j (by omega) hj
  obtain ⟨s₁, he₁, hs₁, hf₁, hr₁, hm₁⟩ := zhermAvg_bin hsem (b := .add) trivial hYsh hlen hs₀ hf₀
    (yo + zidx (.const n) (.var i) (.var j)) ⟨X, xo + zidx (.const n) (.var i) (.var j)⟩
    ⟨X, xo + zidx (.const n) (.var j) (.var i)⟩ (2 * (i + n * j)) (by omega) rfl
    (hX _ hf₀ i j (by omega) hj).1
    (((hX _ hf₀ j i hj (by omega)).1).imp fun _ h => ⟨h, nofun⟩)
  obtain ⟨s₂, he₂, hs₂, hf₂, hr₂, hm₂⟩ := zhermAvg_bin hsem (b := .div) trivial hYsh hlen
    (σ := { σ with store := s₁, cnt := _ }) hs₁ hf₁
    (yo + zidx (.const n) (.var i) (.var j)) ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
    c (2 * (i + n * j)) (by omega) rfl hr₁ (hC _ hf₁)
  obtain ⟨s₃, he₃, hs₃, hf₃, hr₃, hm₃⟩ := zhermAvg_bin hsem (b := .sub) trivial hYsh hlen
    (σ := { σ with store := s₂, cnt := _ }) hs₂ hf₂
    (yo + zidx (.const n) (.var i) (.var j) + 1)
    ⟨X, xo + zidx (.const n) (.var i) (.var j) + 1⟩
    ⟨X, xo + zidx (.const n) (.var j) (.var i) + 1⟩ (2 * (i + n * j) + 1) hk rfl
    (hX _ hf₂ i j (by omega) hj).2
    (((hX _ hf₂ j i hj (by omega)).2).imp fun _ h => ⟨h, nofun⟩)
  obtain ⟨s₄, he₄, hs₄, hf₄, hr₄, hm₄⟩ := zhermAvg_bin hsem (b := .div) trivial hYsh hlen
    (σ := { σ with store := s₃, cnt := _ }) hs₃ hf₃
    (yo + zidx (.const n) (.var i) (.var j) + 1)
    ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩ c (2 * (i + n * j) + 1) hk rfl
    hr₃ (hC _ hf₃)
  exact ⟨_, (he₁ _).trans ((he₂ _).trans ((he₃ _).trans ((he₄ _).trans (exec_skip I _)))),
    hs₄, hf₄, ⟨hm₄ _ (hm₃ _ hr₂), hr₄⟩, fun k' h => hm₄ _ (hm₃ _ (hm₂ _ (hm₁ _ h)))⟩

/-- **`zhermAvg` succeeds** under the standard model with every value in range, when $c$ decodes
to a nonzero value and the buffer `Y` at tag `p` is long enough (every addition, subtraction,
negation and literal then succeeds, and every division by $c$). No printed source.
Proof: as `NLAlib.Computation.exists_exec_zhermShift`, each operation by `bin_ok`, `lit_ok`,
`neg` of `NLAlib.Computation.IsRelErrSem` (`trivial` for the range). M, about 45 lines. -/
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
    ⟨⟨_, (hs _ _ _ (zhermAvg_disj hXY (by have := hn i j hi hj; omega))).trans
        (hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨0, Nat.zero_lt_two⟩)⟩,
      ⟨_, (hs _ _ _ (zhermAvg_disj hXY (hn i j hi hj))).trans
        (hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨1, Nat.one_lt_two⟩)⟩⟩
  have hC : ∀ s : Store P K, (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      s.read q b i = st.store.read q b i) →
      ∃ c', s.read p c.buf c.idx.eval = some c' ∧ (BinOp.div = .div → dec p c' ≠ 0) :=
    fun s hs => ⟨cv, (hs _ _ _ hcY).trans hc, fun _ => hcv⟩
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) _))) .skip) st =
    some st'
  rw [exec_seq_skip, exec_named, exec_seq]
  -- the strict upper triangle
  refine zhermAvg_bind (fun σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
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
  refine zhermAvg_bind (fun σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
    (exists_exec_loop_eq_some_of_forall I (fun _ σ => Fr σ ∧ Up σ fun i' j' => i' < j' ∧ j' < n)
      ⟨hσ₁, hup₁⟩ (fun i hi σ ⟨⟨hs₀, hf₀⟩, hup⟩ => by
        have hi : i < n := hi
        have hk := hn i i hi hi
        obtain ⟨s₁, he₁, hs₁, hf₁, hr₁, hm₁⟩ := zhermAvg_bin hsem (b := .add) trivial hYsh hlen
          hs₀ hf₀
          (yo + zidx (.const n) (.var i) (.var i)) ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩
          ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩ (2 * (i + n * i)) (by omega) rfl
          (hX _ hf₀ i i hi hi).1 (((hX _ hf₀ i i hi hi).1).imp fun _ h => ⟨h, nofun⟩)
        obtain ⟨s₂, he₂, hs₂, hf₂, -, hm₂⟩ := zhermAvg_bin hsem (b := .div) trivial hYsh hlen
          (σ := { σ with store := s₁, cnt := _ }) hs₁ hf₁
          (yo + zidx (.const n) (.var i) (.var i)) ⟨Y, yo + zidx (.const n) (.var i) (.var i)⟩
          c (2 * (i + n * i)) (by omega) rfl hr₁ (hC _ hf₁)
        obtain ⟨s₃, he₃, hs₃, hf₃, hm₃⟩ := zhermAvg_lit hsem hYsh hlen
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

/-! ### The max-modulus test -/

private theorem zboxTest_lit {p : P} {f : Cell ℕ ℕ} {s s₂ st : St P K C} {q : ℚ}
    (hsh : s.store.shape = st.store.shape) (hpos : s.pos = st.pos)
    (hfr : ∀ q b i, (b ≠ f.buf ∨ i ≠ f.idx.eval) → s.store.read q b i = st.store.read q b i)
    (hex : exec I (.seq (.instr (.lit p f q)) .skip) s = some s₂) :
    s₂.store.shape = st.store.shape ∧ s₂.pos = st.pos ∧
      (∀ q b i, (b ≠ f.buf ∨ i ≠ f.idx.eval) → s₂.store.read q b i = st.store.read q b i) ∧
      s₂.store.read p f.buf f.idx.eval = some ((I.sem.lit p q).getD default) := by
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  exact ⟨(Store.shape_of_write_eq_some hw').trans hsh, hpos,
    fun q b i hb => (Store.read_of_write_eq_some_of_ne hw' hb).trans (hfr q b i hb),
    by rw [Store.read_of_write_eq_some hw', hv, Option.getD_some]⟩

omit [Inhabited K] in
private theorem zboxTest_forall_iff {p : P} {m n X off : ℕ} {s : Store P K}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds s p X off A) (le : K → K → Bool)
    (ℓ h : K) :
    (∀ k < 2 * (m * n), ∀ x, s.read p X (off + k) = some x → le ℓ x = true ∧ le x h = true) ↔
      ((List.finRange m).all fun i => (List.finRange n).all fun j =>
        le ℓ (A i j).1 && le (A i j).1 h && le ℓ (A i j).2 && le (A i j).2 h) = true := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true]
  constructor
  · intro hT i j
    have hj := Nat.mul_le_mul_left m (show j.1 + 1 ≤ n from j.2)
    rw [Nat.mul_succ] at hj
    have h1 := hT (2 * (i.1 + m * j.1) + 0) (by omega) _ (hA i j ⟨0, Nat.two_pos⟩)
    have h2 := hT (2 * (i.1 + m * j.1) + 1) (by omega) _ (hA i j ⟨1, Nat.one_lt_two⟩)
    exact ⟨⟨⟨h1.1, h1.2⟩, h2.1⟩, h2.2⟩
  · intro hall k hk x hx
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
    set i₀ : Fin m := ⟨k / 2 % m, Nat.mod_lt _ hm⟩
    set j₀ : Fin n := ⟨k / 2 / m, Nat.div_lt_of_lt_mul (by omega)⟩
    have e : 2 * (i₀.1 + m * j₀.1) + k % 2 = k := by
      change 2 * (k / 2 % m + m * (k / 2 / m)) + k % 2 = k
      rw [Nat.mod_add_div]; omega
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hall i₀ j₀
    obtain ⟨t, ht⟩ : ∃ t : Fin pairLayout.width,
        s.read p X (off + k) = some (pairLayout.put (A i₀ j₀) t) :=
      ⟨_, e ▸ hA i₀ j₀ ⟨_, Nat.mod_lt _ two_pos⟩⟩
    rw [hx, Option.some_inj] at ht
    subst ht
    obtain ⟨t, htl⟩ := t
    change t < 2 at htl
    rcases t with _ | _ | t
    exacts [⟨a1, a2⟩, ⟨a3, a4⟩, by omega]

private theorem zboxTest_cell_ne {b i c k len t k' : ℕ}
    (h : blockDisjoint (b, i, 1) (c, k, len) = true) (ht : t < len) (he : k' = k + t) :
    c ≠ b ∨ k' ≠ i := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h
  by_cases hb : c = b
  · exact Or.inr (by omega)
  · exact Or.inl hb

/-- **`zboxTest` computes the machine's test**: a successful run of
`NLAlib.Computation.zboxTest` from a state whose block at `X` holds the complex $m \times n$
matrix $\mathbf{A}$ and whose cells `lo`, `hi` hold $\ell$, $h$, with the flag cell outside the
block and distinct from `lo` and `hi`, ends with the flag holding the machine's zero if every
part $t$ of every entry has $\ell \le t$ and $t \le h$ by the machine's comparisons, and the
machine's one otherwise, every other cell unchanged, the same store shape and the same tape
positions. No printed source.
Proof: after the literal $0$, the word loop keeps the invariant "the flag holds zero if every
part below $w$ passes, one otherwise" (`NLAlib.Computation.forall_of_exec_loop_eq_some`,
scaffold); each step is two `NLAlib.Computation.exec_ite` with the comparisons read off
(`Option.getD_some`); the flat word order covers the parts of every entry once, and
`List.all_eq_true` with `NLAlib.Computation.pairLayout.holds_iff` (scaffold) matches the nested
`List.finRange` test. M, about 70 lines. -/
theorem read_of_exec_zboxTest (p : P) (m n : ℕ) {X : ℕ} {xo : IExp ℕ} {lo hi f : Cell ℕ ℕ}
    {ℓ h : K} {st st' : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hlo : st.store.read p lo.buf lo.idx.eval = some ℓ)
    (hhi : st.store.read p hi.buf hi.idx.eval = some h)
    (hfX : blockDisjoint (f.buf, f.idx.eval, 1) (X, xo.eval, 2 * (m * n)) = true)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true)
    (hrun : exec I (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    st'.store.read p f.buf f.idx.eval = some
      (if (List.finRange m).all (fun i => (List.finRange n).all fun j =>
          M.le ℓ (A i j).1 && M.le (A i j).1 h && M.le ℓ (A i j).2 && M.le (A i j).2 h) then
        M.zero else M.one) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (f.buf, f.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M
  classical
  have hprog : (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run = .seq (.named
      "zboxTest" [.idx (.const m), .idx (.const n), .buf X, .idx xo, .cell lo, .cell hi, .cell f]
      (.seq (.instr (.lit p f 0)) (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.ite p .le lo ⟨X, xo + .var w⟩
          (.seq (.ite p .le ⟨X, xo + .var w⟩ hi .skip (.seq (.instr (.lit p f 1)) .skip)) .skip)
          (.seq (.instr (.lit p f 1)) .skip)) .skip) .skip))) .skip := rfl
  rw [hprog, exec_seq_skip, exec_named, exec_seq, ← exec_seq_skip I (.instr _),
    Option.bind_eq_some_iff] at hrun
  obtain ⟨s₀, h₀, hrun⟩ := hrun
  rw [exec_seq_skip] at hrun
  let T : ℕ → Prop := fun w => ∀ k < w, ∀ x, st.store.read p X (xo.eval + k) = some x →
    M.le ℓ x = true ∧ M.le x h = true
  have key := zboxTest_forall_iff (p := p) hA M.le ℓ h
  obtain ⟨sh₀, pos₀, fr₀, fl₀⟩ := zboxTest_lit rfl rfl (fun _ _ _ _ => rfl) h₀
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I
    (fun w s => s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
      (∀ q b i, (b ≠ f.buf ∨ i ≠ f.idx.eval) → s.store.read q b i = st.store.read q b i) ∧
      s.store.read p f.buf f.idx.eval = some (if T w then M.zero else M.one))
    ⟨sh₀, pos₀, fr₀, fl₀.trans (by rw [if_pos (fun k hk => absurd hk (Nat.not_lt_zero _))]; rfl)⟩
    ?_ hrun)
  · obtain ⟨hsh, hpos, hfr, hfl⟩ := hR
    simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hfl
    exact ⟨hfl.trans (congrArg some (if_congr key rfl rfl)), fun q b i hb => hfr q b i
      ((zboxTest_cell_ne (k' := f.idx.eval) hb Nat.one_pos rfl).imp Ne.symm Ne.symm), hsh, hpos⟩
  rintro w hw s₁ s₂ ⟨hsh, hpos, hfr, hfl⟩ hex
  rw [exec_seq_skip, exec_ite] at hex
  simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨a, ha, x, hx, r, hr, rfl⟩, hex⟩ := hex
  simp only [IExp.eval_add, IExp.eval_var, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    at hx hw
  have hxst : st.store.read p X (xo.eval + w) = some x :=
    (hfr _ _ _ (zboxTest_cell_ne hfX hw rfl)).symm.trans hx
  rw [hfr _ _ _ (zboxTest_cell_ne (k' := lo.idx.eval) hflo Nat.one_pos rfl), hlo,
    Option.some_inj] at ha
  subst ha
  have hr' : M.le ℓ x = r := by simp only [M, ScalarSem.toFloatMachine, hr, Option.getD_some]
  cases r
  · simp only [Bool.false_eq_true, if_false] at hex
    obtain ⟨sh, ps, fr, fl⟩ := zboxTest_lit (by exact hsh) (by exact hpos) (by exact hfr) hex
    refine ⟨sh, ps, fr, fl.trans ?_⟩
    rw [if_neg fun hT => absurd ((hT w (by omega) x hxst).1.symm.trans hr') (by simp)]
    rfl
  simp only [if_true] at hex
  rw [exec_seq_skip, exec_ite] at hex
  simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨b, hb, c, hc, r, hr₂, rfl⟩, hex⟩ := hex
  simp only [IExp.eval_add, IExp.eval_var] at hb
  rw [hx, Option.some_inj] at hb
  subst hb
  rw [hfr _ _ _ (zboxTest_cell_ne (k' := hi.idx.eval) hfhi Nat.one_pos rfl), hhi,
    Option.some_inj] at hc
  subst hc
  have hr₂' : M.le x h = r := by simp only [M, ScalarSem.toFloatMachine, hr₂, Option.getD_some]
  cases r
  · simp only [Bool.false_eq_true, if_false] at hex
    obtain ⟨sh, ps, fr, fl⟩ := zboxTest_lit (by exact hsh) (by exact hpos) (by exact hfr) hex
    refine ⟨sh, ps, fr, fl.trans ?_⟩
    rw [if_neg fun hT => absurd ((hT w (by omega) x hxst).2.symm.trans hr₂') (by simp)]
    rfl
  simp only [if_true, exec_skip, Option.some_inj] at hex
  subst hex
  refine ⟨hsh, hpos, hfr, hfl.trans (congrArg some (if_congr ?_ rfl rfl))⟩
  refine ⟨fun hT k hk y hy => ?_, fun hT k hk => hT k (by omega)⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
  · exact hT k hk y hy
  · rw [hxst, Option.some_inj] at hy
    subst hy
    exact ⟨hr', hr₂'⟩

/-- **`zboxTest` succeeds** under the standard model with every value in range, when the flag cell
can be written. No printed source.
Proof: as `NLAlib.Computation.exists_exec_zcopy`, the invariant "the store has the shape of
`st`", each step two `NLAlib.Computation.exec_ite` (`cmp_le`), the literals by `lit_ok`. S, about
25 lines. -/
theorem exists_exec_zboxTest (p : P) (m n : ℕ) {X : ℕ} {xo : IExp ℕ} {lo hi f : Cell ℕ ℕ}
    {ℓ h : K} {st : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hlo : st.store.read p lo.buf lo.idx.eval = some ℓ)
    (hhi : st.store.read p hi.buf hi.idx.eval = some h)
    (hfX : blockDisjoint (f.buf, f.idx.eval, 1) (X, xo.eval, 2 * (m * n)) = true)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hf : ∃ s, st.store.write p f.buf f.idx.eval default = some s) :
    ∃ st', exec I (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run st = some st' := by
  obtain ⟨s₀, hs₀⟩ := hf
  obtain ⟨z₀, hz₀⟩ := hsem.lit_ok p 0 trivial
  obtain ⟨z₁, hz₁⟩ := hsem.lit_ok p 1 trivial
  have hX : ∀ k < 2 * (m * n), ∃ v, st.store.read p X (xo.eval + k) = some v := by
    intro k hk
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
    have e : 2 * (k / 2 % m + m * (k / 2 / m)) + k % 2 = k := by rw [Nat.mod_add_div]; omega
    exact ⟨_, e ▸ hA ⟨_, Nat.mod_lt _ hm⟩ ⟨_, Nat.div_lt_of_lt_mul (by omega)⟩
      ⟨_, Nat.mod_lt _ two_pos⟩⟩
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hfX hflo hfhi
  let R : St P K C → Prop := fun s => s.store.shape = st.store.shape ∧
    (∀ k < 2 * (m * n), s.store.read p X (xo.eval + k) = st.store.read p X (xo.eval + k)) ∧
    s.store.read p lo.buf lo.idx.eval = some ℓ ∧ s.store.read p hi.buf hi.idx.eval = some h
  have hR : ∀ (s : St P K C) (q : ℚ) (z : K), R s → I.sem.lit p q = some z →
      ∃ s', exec I (.seq (.instr (.lit p f q)) .skip) s = some s' ∧ R s' := by
    rintro s q z ⟨hsh, hsX, hslo, hshi⟩ hz
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_shape_eq hsh hs₀ z
    refine ⟨_, (exec_seq_instr_lit I hz hs').trans (exec_skip I _),
      (Store.shape_of_write_eq_some hs').trans hsh, fun k hk => ?_, ?_, ?_⟩
    · refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans (hsX k hk)
      by_cases hb : X = f.buf
      · exact Or.inr (by omega)
      · exact Or.inl hb
    · refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans hslo
      by_cases hb : lo.buf = f.buf
      · exact Or.inr (by omega)
      · exact Or.inl hb
    · refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans hshi
      by_cases hb : hi.buf = f.buf
      · exact Or.inr (by omega)
      · exact Or.inl hb
  have hrun : (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run = .seq (.named
      "zboxTest" [.idx (.const m), .idx (.const n), .buf X, .idx xo, .cell lo, .cell hi, .cell f]
      (.seq (.instr (.lit p f 0)) (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.ite p .le lo ⟨X, xo + .var w⟩
          (.seq (.ite p .le ⟨X, xo + .var w⟩ hi .skip (.seq (.instr (.lit p f 1)) .skip)) .skip)
          (.seq (.instr (.lit p f 1)) .skip)) .skip) .skip))) .skip := rfl
  obtain ⟨s₁, h₁, hR₁⟩ := hR st 0 z₀ ⟨rfl, fun _ _ => rfl, hlo, hhi⟩ (by exact_mod_cast hz₀)
  rw [hrun, exec_seq_skip, exec_named, exec_seq, ← exec_seq_skip, h₁, Option.bind_some,
    exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I (fun _ s => R s) hR₁ ?_).imp fun _ h => h.1
  rintro w hw s hs
  simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hw
  obtain ⟨v, hv⟩ := hX w hw
  have hxv : s.store.read p X (xo.eval + w) = some v := (hs.2.1 w hw).trans hv
  rw [exec_seq_skip, exec_ite]
  simp only [cmpStep, hs.2.2.1, IExp.eval_add, IExp.eval_var, hxv, hsem.cmp_le,
    Option.bind_some, Option.map_some]
  split_ifs
  · rw [exec_seq_skip, exec_ite]
    simp only [cmpStep, hs.2.2.2, IExp.eval_add, IExp.eval_var, hxv, hsem.cmp_le,
      Option.bind_some, Option.map_some]
    split_ifs
    · exact ⟨_, exec_skip I _, hs⟩
    · exact hR _ 1 z₁ hs (by exact_mod_cast hz₁)
  · exact hR _ 1 z₁ hs (by exact_mod_cast hz₁)

/-! ### Kernels for later stages: identity, sums, scaling, conjugate transpose, trace -/

/-- **`zidentity` writes the stored identity**: a successful run of
`NLAlib.Computation.zidentity` ends with the block at `Y` holding the machine's identity matrix
(`NLAlib.FloatMachine.identityMat`), every cell outside it unchanged. No printed source.
Proof: `NLAlib.Computation.holds_of_exec_zzero`'s loop, then a loop of literals $1$ at the
diagonal real parts (the indices $2(i + ni)$ are distinct, `omega`). M, about 35 lines. -/
theorem holds_of_exec_zidentity (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st st' : St P K C}
    (h : exec I (zidentity (ι := ι) p (.const n) Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).identityMat n) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  sorry

/-- **`zadd` adds the parts**: a successful run of `NLAlib.Computation.zadd` from blocks at `X`,
`Y` holding $\mathbf{A}$, $\mathbf{B}$, into a block at `Z` disjoint from both or equal to one of
them, ends with the block at `Z` holding the entrywise machine sums of the real and of the
imaginary parts, every cell outside it unchanged. No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zneg`. M, about 40 lines. -/
theorem holds_of_exec_zadd (p : P) (m n : ℕ) {X Y Z : ℕ} {xo yo zo : IExp ℕ} {st st' : St P K C}
    {A B : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hB : pairLayout.Holds st.store p Y yo.eval B)
    (hZX : blockDisjoint (Z, zo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Z = X ∧ zo.eval = xo.eval))
    (hZY : blockDisjoint (Z, zo.eval, 2 * (m * n)) (Y, yo.eval, 2 * (m * n)) = true ∨
      (Z = Y ∧ zo.eval = yo.eval))
    (h : exec I (zadd (ι := ι) p (.const m) (.const n) X xo Y yo Z zo).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Z zo.eval
      (Matrix.of fun i j => (M.add (A i j).1 (B i j).1, M.add (A i j).2 (B i j).2)) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Z, zo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  intro M
  have hrun : (zadd (ι := ι) p (.const m) (.const n) X xo Y yo Z zo).run = .seq (.named "zadd"
      [.idx (.const m), .idx (.const n), .buf X, .idx xo, .buf Y, .idx yo, .buf Z, .idx zo]
      (.seq (.loop (2 * (.const m * .const n)) fun w =>
        .seq (.instr (.bin p .add ⟨Z, zo + .var w⟩ ⟨X, xo + .var w⟩ ⟨Y, yo + .var w⟩)) .skip)
        .skip)) .skip := rfl
  rw [hrun, exec_seq_skip, exec_named, exec_seq_skip] at h
  have hdis : ∀ {W : ℕ} {wo : IExp ℕ},
      (blockDisjoint (Z, zo.eval, 2 * (m * n)) (W, wo.eval, 2 * (m * n)) = true ∨
        (Z = W ∧ zo.eval = wo.eval)) →
      ∀ w < 2 * (m * n), W ≠ Z ∨ wo.eval + w < zo.eval ∨ zo.eval + w ≤ wo.eval + w := by
    intro W wo hW w hw
    rcases hW with hW | ⟨rfl, he⟩
    · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hW
      by_cases hb : W = Z
      · exact Or.inr (by omega)
      · exact Or.inl hb
    · exact Or.inr (by omega)
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I
    (fun w s => (∀ k < w, s.store.read p Z (zo.eval + k) =
        (st.store.read p X (xo.eval + k)).bind fun a =>
          (st.store.read p Y (yo.eval + k)).map (M.add a)) ∧
      ∀ q b i, (b ≠ Z ∨ i < zo.eval ∨ zo.eval + w ≤ i) →
        s.store.read q b i = st.store.read q b i)
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h)
  · obtain ⟨hZ, hfr⟩ := hR
    simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hZ hfr
    refine ⟨fun i j t => ?_, fun q b i hb => hfr q b i ?_⟩
    · have hj := Nat.mul_le_mul_left m (show j.1 + 1 ≤ n from j.2)
      have ht : t.1 < 2 := t.2
      rw [Nat.mul_succ] at hj
      have hk : 2 * (i.1 + m * j.1) + t.1 < 2 * (m * n) := by omega
      refine (hZ _ hk).trans ?_
      rw [show st.store.read p X (xo.eval + (2 * (i.1 + m * j.1) + t.1)) = _ from hA i j t,
        show st.store.read p Y (yo.eval + (2 * (i.1 + m * j.1) + t.1)) = _ from hB i j t,
        Option.bind_some, Option.map_some]
      obtain ⟨t, ht⟩ := t
      change t < 2 at ht
      rcases t with _ | _ | t
      · rfl
      · rfl
      · omega
    · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hb
      by_cases hbZ : b = Z
      · exact Or.inr (by omega)
      · exact Or.inl hbZ
  rintro w hw s₁ s₂ ⟨hZ, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨a, ha, c, hc, v, hv, s', hw', rfl⟩, rfl⟩ := hex
  simp only [IExp.eval_add, IExp.eval_var] at ha hc hw'
  simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hw
  refine ⟨fun k hk => ?_,
    fun q b i hb => (Store.read_of_write_eq_some_of_ne hw' ?_).trans (hfr q b i ?_)⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact (Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega))).trans (hZ k hk)
    · rw [Store.read_of_write_eq_some hw', ← hfr _ _ _ (hdis hZX k hw), ha, Option.bind_some,
        ← hfr _ _ _ (hdis hZY k hw), hc, Option.map_some]
      simp only [M, ScalarSem.toFloatMachine, hv, Option.getD_some]
  · by_cases hbZ : b = Z
    · exact Or.inr (by omega)
    · exact Or.inl hbZ
  · omega

/-- **`zsub` subtracts the parts**: as `NLAlib.Computation.holds_of_exec_zadd`, with the
machine's subtraction. No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zadd`. M, about 40 lines. -/
theorem holds_of_exec_zsub (p : P) (m n : ℕ) {X Y Z : ℕ} {xo yo zo : IExp ℕ} {st st' : St P K C}
    {A B : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hB : pairLayout.Holds st.store p Y yo.eval B)
    (hZX : blockDisjoint (Z, zo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Z = X ∧ zo.eval = xo.eval))
    (hZY : blockDisjoint (Z, zo.eval, 2 * (m * n)) (Y, yo.eval, 2 * (m * n)) = true ∨
      (Z = Y ∧ zo.eval = yo.eval))
    (h : exec I (zsub (ι := ι) p (.const m) (.const n) X xo Y yo Z zo).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Z zo.eval
      (Matrix.of fun i j => (M.sub (A i j).1 (B i j).1, M.sub (A i j).2 (B i j).2)) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Z, zo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  intro M
  have key : (zsub (ι := ι) p (.const m) (.const n) X xo Y yo Z zo).run = .seq
      (.named "zsub" [.idx (.const m), .idx (.const n), .buf X, .idx xo, .buf Y, .idx yo,
        .buf Z, .idx zo] (.seq (.loop (2 * (IExp.const m * IExp.const n)) fun w => .seq
          (.instr (.bin p .sub ⟨Z, zo + .var w⟩ ⟨X, xo + .var w⟩ ⟨Y, yo + .var w⟩)) .skip) .skip))
      .skip := rfl
  rw [key, exec_seq_skip, exec_named, exec_seq_skip] at h
  -- one word of the loop: the read operands, the write and the position
  have bstep : ∀ (k : ℕ) (s₁ s₂ : St P K C),
      exec I (.seq (.instr (.bin p .sub ⟨Z, zo + .var k⟩ ⟨X, xo + .var k⟩ ⟨Y, yo + .var k⟩))
        .skip) s₁ = some s₂ →
      ∃ a c s, s₁.store.read p X (xo.eval + k) = some a ∧
        s₁.store.read p Y (yo.eval + k) = some c ∧
        s₁.store.write p Z (zo.eval + k) (M.sub a c) = some s ∧
        s₂.store = s ∧ s₂.pos = s₁.pos := by
    intro k s₁ s₂ hr
    obtain ⟨a, ha⟩ : ∃ a, s₁.store.read p X (xo.eval + k) = some a := by
      cases hx : s₁.store.read p X (xo.eval + k) with
      | none => simp [exec_seq, exec_instr, Instr.run, hx] at hr
      | some a => exact ⟨a, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, s₁.store.read p Y (yo.eval + k) = some c := by
      cases hy : s₁.store.read p Y (yo.eval + k) with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hy] at hr
      | some c => exact ⟨c, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, I.sem.bin p .sub a c = some v := by
      cases hb : I.sem.bin p .sub a c with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hc, hb] at hr
      | some v => exact ⟨v, rfl⟩
    obtain ⟨s, hw⟩ : ∃ s, s₁.store.write p Z (zo.eval + k) v = some s := by
      cases hw : s₁.store.write p Z (zo.eval + k) v with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hc, hv, hw] at hr
      | some s => exact ⟨s, rfl⟩
    have hMv : M.sub a c = v := by
      show (I.sem.bin p .sub a c).getD default = v
      rw [hv]; rfl
    rw [exec_seq_instr_bin (dst := ⟨Z, zo + .var k⟩) I ha hc hv hw, exec_skip] at hr
    cases hr
    exact ⟨a, c, s, ha, hc, hMv ▸ hw, rfl, rfl⟩
  -- distinct words of the loop are distinct cells, of the output block and of the inputs
  have dis : ∀ k w, k < 2 * (m * n) → w < 2 * (m * n) → w ≠ k →
      (X ≠ Z ∨ xo.eval + w ≠ zo.eval + k) ∧ (Y ≠ Z ∨ yo.eval + w ≠ zo.eval + k) := by
    intro k w hk hw hwk
    refine ⟨?_, ?_⟩
    · rcases hZX with h | ⟨h1, h2⟩
      · by_cases hXZ : X = Z
        · right
          subst hXZ
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at h
          omega
        · exact Or.inl hXZ
      · right; omega
    · rcases hZY with h | ⟨h1, h2⟩
      · by_cases hYZ : Y = Z
        · right
          subst hYZ
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at h
          omega
        · exact Or.inl hYZ
      · right; omega
  have inv := forall_of_exec_loop_eq_some (I := I) (fun k s₁ =>
      (∀ w < k, ∃ a c, st.store.read p X (xo.eval + w) = some a ∧
          st.store.read p Y (yo.eval + w) = some c ∧
          s₁.store.read p Z (zo.eval + w) = some (M.sub a c)) ∧
      (∀ w, k ≤ w → w < 2 * (m * n) →
          s₁.store.read p X (xo.eval + w) = st.store.read p X (xo.eval + w)) ∧
      (∀ w, k ≤ w → w < 2 * (m * n) →
          s₁.store.read p Y (yo.eval + w) = st.store.read p Y (yo.eval + w)) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Z, zo.eval, 2 * (m * n)) = true →
          s₁.store.read q b i = st.store.read q b i) ∧
      s₁.store.shape = st.store.shape ∧ s₁.pos = st.pos) ?_ ?_ h
  rotate_left
  · refine ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun w _ _ => rfl, fun w _ _ => rfl,
      fun q b i _ => rfl, rfl, rfl⟩
  · intro k hk s₁ s₂ ⟨hZ, hX, hY, hout, hsh, hpos⟩ hr
    have hk2 : k < 2 * (m * n) := hk
    obtain ⟨a, c, s, ha, hc, hw, hs, hp⟩ := bstep k s₁ s₂ hr
    have ha' : st.store.read p X (xo.eval + k) = some a := by
      rw [← hX k le_rfl hk]; exact ha
    have hc' : st.store.read p Y (yo.eval + k) = some c := by
      rw [← hY k le_rfl hk]; exact hc
    have hXn : ∀ w, k + 1 ≤ w → w < 2 * (m * n) →
        s₂.store.read p X (xo.eval + w) = st.store.read p X (xo.eval + w) := by
      intro w hw1 hw2
      rw [hs, Store.read_of_write_eq_some_of_ne hw (dis k w hk hw2 (by omega)).1,
        hX w (by omega) hw2]
    have hYn : ∀ w, k + 1 ≤ w → w < 2 * (m * n) →
        s₂.store.read p Y (yo.eval + w) = st.store.read p Y (yo.eval + w) := by
      intro w hw1 hw2
      rw [hs, Store.read_of_write_eq_some_of_ne hw (dis k w hk hw2 (by omega)).2,
        hY w (by omega) hw2]
    have hZn : ∀ w < k + 1, ∃ a' c', st.store.read p X (xo.eval + w) = some a' ∧
        st.store.read p Y (yo.eval + w) = some c' ∧
        s₂.store.read p Z (zo.eval + w) = some (M.sub a' c') := by
      intro w hw1
      rcases Nat.lt_or_ge w k with hlt | hge
      · obtain ⟨a', c', hxa, hyc, hz⟩ := hZ w hlt
        refine ⟨a', c', hxa, hyc, ?_⟩
        rw [hs, Store.read_of_write_eq_some_of_ne hw
          (Or.inr (show zo.eval + w ≠ zo.eval + k by omega) : Z ≠ Z ∨ zo.eval + w ≠ zo.eval + k)]
        exact hz
      · have hwk : w = k := by omega
        subst hwk
        exact ⟨a, c, ha', hc', by rw [hs, Store.read_of_write_eq_some hw]⟩
    have hout' : ∀ q b i, blockDisjoint (b, i, 1) (Z, zo.eval, 2 * (m * n)) = true →
        s₂.store.read q b i = st.store.read q b i := by
      intro q b i hd
      have hne : b ≠ Z ∨ i ≠ zo.eval + k := by
        by_cases hb : b = Z
        · right
          subst hb
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at hd
          omega
        · exact Or.inl hb
      rw [hs, Store.read_of_write_eq_some_of_ne hw hne]
      exact hout q b i hd
    exact ⟨hZn, hXn, hYn, hout', by rw [hs, Store.shape_of_write_eq_some hw, hsh],
      by rw [hp, hpos]⟩
  obtain ⟨hZ, hX, hY, hout, hsh, hpos⟩ := inv
  have hbnd : ∀ (i : Fin m) (j : Fin n) (t : Fin 2),
      2 * ((i : ℕ) + m * j) + (t : ℕ) < 2 * (m * n) := by
    intro i j t
    have h1 : (i : ℕ) + m * j < m * n := by
      nlinarith [i.isLt, j.isLt, Nat.mul_le_mul_left m (show (j : ℕ) + 1 ≤ n from j.isLt)]
    have := t.isLt
    omega
  refine ⟨fun i j (t : Fin 2) => ?_, hout⟩
  obtain ⟨a, c, hxa, hyc, hz⟩ := hZ _ (hbnd i j t)
  have ha : a = pairLayout.put (A i j) t := Option.some.inj (hxa.symm.trans (hA i j t))
  have hc : c = pairLayout.put (B i j) t := Option.some.inj (hyc.symm.trans (hB i j t))
  rw [ha, hc] at hz
  convert hz using 2 <;> fin_cases t <;> simp [pairLayout]

/-- **`zscal` scales the parts**: a successful run of `NLAlib.Computation.zscal` from a block at
`X` holding $\mathbf{A}$ and a cell `a` holding $a$, into a block at `Y` disjoint from `a` and
disjoint from or equal to the block at `X`, ends with the block at `Y` holding the entrywise
machine products of $a$ with both parts, every cell outside it unchanged. No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zneg`. M, about 40 lines. -/
theorem holds_of_exec_zscal (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {a : Cell ℕ ℕ} {av : K}
    {st st' : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (ha : st.store.read p a.buf a.idx.eval = some av)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Y = X ∧ yo.eval = xo.eval))
    (haY : blockDisjoint (a.buf, a.idx.eval, 1) (Y, yo.eval, 2 * (m * n)) = true)
    (h : exec I (zscal (ι := ι) p (.const m) (.const n) a X xo Y yo).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Y yo.eval
      (Matrix.of fun i j => (M.mul av (A i j).1, M.mul av (A i j).2)) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  intro M
  have key : (zscal (ι := ι) p (.const m) (.const n) a X xo Y yo).run = .seq
      (.named "zscal" [.idx (.const m), .idx (.const n), .cell a, .buf X, .idx xo, .buf Y,
        .idx yo] (.seq (.loop (2 * (IExp.const m * IExp.const n)) fun w => .seq
          (.instr (.bin p .mul ⟨Y, yo + .var w⟩ a ⟨X, xo + .var w⟩)) .skip) .skip))
      .skip := rfl
  rw [key, exec_seq_skip, exec_named, exec_seq_skip] at h
  -- one word of the loop
  have bstep : ∀ (k : ℕ) (s₁ s₂ : St P K C), s₁.store.read p a.buf a.idx.eval = some av →
      exec I (.seq (.instr (.bin p .mul ⟨Y, yo + .var k⟩ a ⟨X, xo + .var k⟩)) .skip) s₁ =
        some s₂ →
      ∃ x s, s₁.store.read p X (xo.eval + k) = some x ∧
        s₁.store.write p Y (yo.eval + k) (M.mul av x) = some s ∧
        s₂.store = s ∧ s₂.pos = s₁.pos := by
    intro k s₁ s₂ hav hr
    obtain ⟨x, hx⟩ : ∃ x, s₁.store.read p X (xo.eval + k) = some x := by
      cases hx : s₁.store.read p X (xo.eval + k) with
      | none => simp [exec_seq, exec_instr, Instr.run, hav, hx] at hr
      | some x => exact ⟨x, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, I.sem.bin p .mul av x = some v := by
      cases hb : I.sem.bin p .mul av x with
      | none => simp [exec_seq, exec_instr, Instr.run, hav, hx, hb] at hr
      | some v => exact ⟨v, rfl⟩
    obtain ⟨s, hw⟩ : ∃ s, s₁.store.write p Y (yo.eval + k) v = some s := by
      cases hw : s₁.store.write p Y (yo.eval + k) v with
      | none => simp [exec_seq, exec_instr, Instr.run, hav, hx, hv, hw] at hr
      | some s => exact ⟨s, rfl⟩
    have hMv : M.mul av x = v := by
      show (I.sem.bin p .mul av x).getD default = v
      rw [hv]; rfl
    rw [exec_seq_instr_bin (dst := (⟨Y, yo + IExp.var k⟩ : Cell ℕ ℕ))
      (x := a) (y := (⟨X, xo + IExp.var k⟩ : Cell ℕ ℕ)) I hav hx hv hw, exec_skip] at hr
    cases hr
    exact ⟨x, s, hx, hMv ▸ hw, rfl, rfl⟩
  -- distinct words are distinct cells
  have dis : ∀ k w, k < 2 * (m * n) → w < 2 * (m * n) → w ≠ k →
      X ≠ Y ∨ xo.eval + w ≠ yo.eval + k := by
    intro k w hk hw hwk
    rcases hXY with h | ⟨h1, h2⟩
    · by_cases hXY' : X = Y
      · right
        subst hXY'
        simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
          Bool.or_eq_true] at h
        omega
      · exact Or.inl hXY'
    · right; omega
  have inv := forall_of_exec_loop_eq_some (I := I) (fun k s₁ =>
      (∀ w < k, ∃ x, st.store.read p X (xo.eval + w) = some x ∧
          s₁.store.read p Y (yo.eval + w) = some (M.mul av x)) ∧
      (∀ w, k ≤ w → w < 2 * (m * n) →
          s₁.store.read p X (xo.eval + w) = st.store.read p X (xo.eval + w)) ∧
      s₁.store.read p a.buf a.idx.eval = some av ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
          s₁.store.read q b i = st.store.read q b i) ∧
      s₁.store.shape = st.store.shape ∧ s₁.pos = st.pos) ?_ ?_ h
  rotate_left
  · refine ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun w _ _ => rfl, ha,
      fun q b i _ => rfl, rfl, rfl⟩
  · intro k hk s₁ s₂ ⟨hY, hX, hav, hout, hsh, hpos⟩ hr
    have hk2 : k < 2 * (m * n) := hk
    obtain ⟨x, s, hx, hw, hs, hp⟩ := bstep k s₁ s₂ hav hr
    have hx' : st.store.read p X (xo.eval + k) = some x := by
      rw [← hX k le_rfl hk2]; exact hx
    have hXn : ∀ w, k + 1 ≤ w → w < 2 * (m * n) →
        s₂.store.read p X (xo.eval + w) = st.store.read p X (xo.eval + w) := by
      intro w hw1 hw2
      rw [hs, Store.read_of_write_eq_some_of_ne hw (dis k w hk2 hw2 (by omega)),
        hX w (by omega) hw2]
    have hYn : ∀ w < k + 1, ∃ x', st.store.read p X (xo.eval + w) = some x' ∧
        s₂.store.read p Y (yo.eval + w) = some (M.mul av x') := by
      intro w hw1
      rcases Nat.lt_or_ge w k with hlt | hge
      · obtain ⟨x', hxa, hyz⟩ := hY w hlt
        refine ⟨x', hxa, ?_⟩
        rw [hs, Store.read_of_write_eq_some_of_ne hw
          (Or.inr (show yo.eval + w ≠ yo.eval + k by omega) : Y ≠ Y ∨ yo.eval + w ≠ yo.eval + k)]
        exact hyz
      · have hwk : w = k := by omega
        subst hwk
        exact ⟨x, hx', by rw [hs, Store.read_of_write_eq_some hw]⟩
    have hav' : s₂.store.read p a.buf a.idx.eval = some av := by
      rw [hs]
      have hne : a.buf ≠ Y ∨ a.idx.eval ≠ yo.eval + k := by
        by_cases hb : a.buf = Y
        · right
          rw [hb] at haY
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at haY
          omega
        · exact Or.inl hb
      rw [Store.read_of_write_eq_some_of_ne hw hne]
      exact hav
    have hout' : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        s₂.store.read q b i = st.store.read q b i := by
      intro q b i hd
      have hne : b ≠ Y ∨ i ≠ yo.eval + k := by
        by_cases hb : b = Y
        · right
          subst hb
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at hd
          omega
        · exact Or.inl hb
      rw [hs, Store.read_of_write_eq_some_of_ne hw hne]
      exact hout q b i hd
    exact ⟨hYn, hXn, hav', hout', by rw [hs, Store.shape_of_write_eq_some hw, hsh],
      by rw [hp, hpos]⟩
  obtain ⟨hY, hX, hav, hout, hsh, hpos⟩ := inv
  have hbnd : ∀ (i : Fin m) (j : Fin n) (t : Fin 2),
      2 * ((i : ℕ) + m * j) + (t : ℕ) < 2 * (m * n) := by
    intro i j t
    have h1 : (i : ℕ) + m * j < m * n := by
      nlinarith [i.isLt, j.isLt, Nat.mul_le_mul_left m (show (j : ℕ) + 1 ≤ n from j.isLt)]
    have := t.isLt
    omega
  refine ⟨fun i j (t : Fin 2) => ?_, hout⟩
  obtain ⟨x, hxa, hyz⟩ := hY _ (hbnd i j t)
  have hx : x = pairLayout.put (A i j) t := Option.some.inj (hxa.symm.trans (hA i j t))
  rw [hx] at hyz
  convert hyz using 2 <;> fin_cases t <;> simp [pairLayout]

/-- **`zconjTranspose` computes the machine's conjugate transpose**: a successful run of
`NLAlib.Computation.zconjTranspose` from a block at `X` holding the complex $m \times n$ matrix
$\mathbf{A}$, into a block at `Y` disjoint from it, ends with the block at `Y` holding
`M.conjTransposeMat A`, every cell outside it unchanged. No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zcopy`, two nested loops; the output index
$2(i + nj)$ runs over every entry of the $n \times m$ result once. M, about 45 lines. -/
theorem holds_of_exec_zconjTranspose (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ}
    {st st' : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * m)) (X, xo.eval, 2 * (m * n)) = true)
    (h : exec I (zconjTranspose (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).conjTransposeMat A) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * m)) = true →
        st'.store.read q b i = st.store.read q b i := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal with hM
  have key : (zconjTranspose (ι := ι) p (.const m) (.const n) X xo Y yo).run = .seq
      (.named "zconjTranspose" [.idx (.const m), .idx (.const n), .buf X, .idx xo, .buf Y,
        .idx yo] (.seq (.loop (IExp.const m) fun j => .seq (.loop (IExp.const n) fun i =>
          .seq (.instr (.copy p ⟨Y, yo + zidx (IExp.const n) (.var i) (.var j)⟩
            ⟨X, xo + zidx (IExp.const m) (.var j) (.var i)⟩))
          (.seq (.instr (.un p .neg ⟨Y, yo + zidx (IExp.const n) (.var i) (.var j) + 1⟩
            ⟨X, xo + zidx (IExp.const m) (.var j) (.var i) + 1⟩)) .skip)) .skip) .skip))
      .skip := rfl
  rw [key, exec_seq_skip, exec_named, exec_seq_skip] at h
  have hnm : n * m = m * n := Nat.mul_comm n m
  -- the input words lie outside the output block
  have hXout : ∀ x, xo.eval ≤ x → x < xo.eval + 2 * (m * n) →
      blockDisjoint (X, x, 1) (Y, yo.eval, 2 * (n * m)) = true := by
    intro x h1 h2
    by_cases hXY' : X = Y
    · subst hXY'
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
        Bool.or_eq_true] at hXY ⊢
      omega
    · simp [blockDisjoint, hXY']
  -- an input word and an output word are different cells
  have hsep : ∀ x y, xo.eval ≤ x → x < xo.eval + 2 * (m * n) → yo.eval ≤ y →
      y < yo.eval + 2 * (n * m) → (X ≠ Y ∨ x ≠ y) := by
    intro x y h1 h2 h3 h4
    by_cases hXY' : X = Y
    · right
      subst hXY'
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
        Bool.or_eq_true] at hXY
      omega
    · exact Or.inl hXY'
  -- an output word is outside every cell of another block
  have hne_of : ∀ b c x, blockDisjoint (b, c, 1) (Y, yo.eval, 2 * (n * m)) = true →
      yo.eval ≤ x → x < yo.eval + 2 * (n * m) → (b ≠ Y ∨ c ≠ x) := by
    intro b c x hd h1 h2
    by_cases hb : b = Y
    · right
      subst hb
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
        Bool.or_eq_true] at hd
      omega
    · exact Or.inl hb
  -- distinct flat indices $i + nj$ give distinct entries
  have hinj : ∀ i i' j j' : ℕ, i < n → i' < n → i + n * j = i' + n * j' → i = i' ∧ j = j' := by
    intro i i' j j' hi hi' h
    have hn : 0 < n := by omega
    have e1 : i = i' := by
      have := congrArg (· % n) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at this
      exact this
    subst e1
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hn (Nat.add_left_cancel h)⟩
  -- the input entries as stored
  have hXw : ∀ (j : ℕ) (hj : j < m) (i : ℕ) (hi : i < n),
      st.store.read p X (xo.eval + 2 * (j + m * i)) = some (A ⟨j, hj⟩ ⟨i, hi⟩).1 ∧
      st.store.read p X (xo.eval + 2 * (j + m * i) + 1) = some (A ⟨j, hj⟩ ⟨i, hi⟩).2 := by
    intro j hj i hi
    exact ⟨by simpa [pairLayout] using hA ⟨j, hj⟩ ⟨i, hi⟩ (0 : Fin 2),
      by simpa [pairLayout, Nat.add_assoc] using hA ⟨j, hj⟩ ⟨i, hi⟩ (1 : Fin 2)⟩
  -- one entry: the copy of the real part and the negated imaginary part
  have bstep : ∀ (j i : ℕ) (t₁ t₂ : St P K C),
      exec I (.seq (.instr (.copy p ⟨Y, yo + zidx (IExp.const n) (IExp.var i) (IExp.var j)⟩
        ⟨X, xo + zidx (IExp.const m) (IExp.var j) (IExp.var i)⟩))
        (.seq (.instr (.un p .neg ⟨Y, yo + zidx (IExp.const n) (IExp.var i) (IExp.var j) + 1⟩
          ⟨X, xo + zidx (IExp.const m) (IExp.var j) (IExp.var i) + 1⟩)) .skip)) t₁ = some t₂ →
      ∃ (a b : K) (u u' : Store P K), t₁.store.read p X (xo.eval + 2 * (j + m * i)) = some a ∧
        u.read p X (xo.eval + 2 * (j + m * i) + 1) = some b ∧
        t₁.store.write p Y (yo.eval + 2 * (i + n * j)) a = some u ∧
        u.write p Y (yo.eval + 2 * (i + n * j) + 1) (M.neg b) = some u' ∧
        t₂.store = u' ∧ t₂.pos = t₁.pos := by
    intro j i t₁ t₂ hr
    obtain ⟨a, ha⟩ : ∃ a, t₁.store.read p X (xo.eval + 2 * (j + m * i)) = some a := by
      cases hx : t₁.store.read p X (xo.eval + 2 * (j + m * i)) with
      | none => simp [exec_seq, exec_instr, Instr.run, hx, zidx, IExp.eval] at hr
      | some a => exact ⟨a, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, t₁.store.write p Y (yo.eval + 2 * (i + n * j)) a = some u := by
      cases hw : t₁.store.write p Y (yo.eval + 2 * (i + n * j)) a with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hw, zidx, IExp.eval] at hr
      | some u => exact ⟨u, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, u.read p X (xo.eval + 2 * (j + m * i) + 1) = some b := by
      cases hx : u.read p X (xo.eval + 2 * (j + m * i) + 1) with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hu, hx, zidx, IExp.eval] at hr
      | some b => exact ⟨b, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, I.sem.un p .neg b = some v := by
      cases hn : I.sem.un p .neg b with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hu, hb, hn, zidx, IExp.eval] at hr
      | some v => exact ⟨v, rfl⟩
    obtain ⟨u', hu'⟩ : ∃ u', u.write p Y (yo.eval + 2 * (i + n * j) + 1) v = some u' := by
      cases hw : u.write p Y (yo.eval + 2 * (i + n * j) + 1) v with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hu, hb, hv, hw, zidx, IExp.eval] at hr
      | some u' => exact ⟨u', rfl⟩
    have hMn : M.neg b = v := by
      show (I.sem.un p .neg b).getD default = v
      rw [hv]; rfl
    rw [exec_seq_instr_copy (dst := (⟨Y, yo + zidx (IExp.const n) (IExp.var i) (IExp.var j)⟩ :
      Cell ℕ ℕ)) (src := (⟨X, xo + zidx (IExp.const m) (IExp.var j) (IExp.var i)⟩ : Cell ℕ ℕ))
      (t := _) I ha hu, exec_seq_instr_un (dst := (⟨Y, yo + zidx (IExp.const n) (IExp.var i)
        (IExp.var j) + 1⟩ : Cell ℕ ℕ)) (x := (⟨X, xo + zidx (IExp.const m) (IExp.var j)
        (IExp.var i) + 1⟩ : Cell ℕ ℕ)) I hb hv hu', exec_skip] at hr
    cases hr
    exact ⟨a, b, u, u', ha, hb, hu, by rw [hMn]; exact hu', rfl, rfl⟩
  -- the outer loop over the columns $j$; the inner loop over the rows $i$
  have inv := forall_of_exec_loop_eq_some (I := I) (fun j s =>
      (∀ (i : Fin n) (j' : Fin m), (i : ℕ) + n * (j' : ℕ) < n * j →
        s.store.read p Y (yo.eval + 2 * ((i : ℕ) + n * (j' : ℕ))) =
            some ((M.conjTransposeMat A) i j').1 ∧
          s.store.read p Y (yo.eval + 2 * ((i : ℕ) + n * (j' : ℕ)) + 1) =
            some ((M.conjTransposeMat A) i j').2) ∧
      (∀ q b c, blockDisjoint (b, c, 1) (Y, yo.eval, 2 * (n * m)) = true →
        s.store.read q b c = st.store.read q b c) ∧
      s.store.shape = st.store.shape ∧ s.pos = st.pos) ?_ ?_ h
  rotate_left
  · exact ⟨fun i j' hlt => absurd hlt (Nat.not_lt_zero _), fun q b c _ => rfl, rfl, rfl⟩
  · intro j hj s₁ s₂ ⟨hG, hOUT, hsh, hpos⟩ hr
    have hj2 : j < m := hj
    rw [exec_seq_skip] at hr
    have inner := forall_of_exec_loop_eq_some (I := I) (fun i t =>
        (∀ (i' : Fin n) (j' : Fin m), (i' : ℕ) + n * (j' : ℕ) < n * j + i →
          t.store.read p Y (yo.eval + 2 * ((i' : ℕ) + n * (j' : ℕ))) =
              some ((M.conjTransposeMat A) i' j').1 ∧
            t.store.read p Y (yo.eval + 2 * ((i' : ℕ) + n * (j' : ℕ)) + 1) =
              some ((M.conjTransposeMat A) i' j').2) ∧
        (∀ q b c, blockDisjoint (b, c, 1) (Y, yo.eval, 2 * (n * m)) = true →
          t.store.read q b c = st.store.read q b c) ∧
        t.store.shape = s₁.store.shape ∧ t.pos = s₁.pos) ?_ ?_ hr
    rotate_left
    · refine ⟨fun i' j' hlt => ?_, hOUT, rfl, rfl⟩
      obtain ⟨g1, g2⟩ := hG i' j' (by simpa using hlt)
      exact ⟨g1, g2⟩
    · intro i hi t₁ t₂ ⟨hG', hOUT', hsh', hpos'⟩ hr'
      have hi2 : i < n := hi
      obtain ⟨a, b, u, u', ha, hb, hu, hu', hs2, hp2⟩ := bstep j i t₁ t₂ hr'
      have hm1 : m * i + m ≤ m * n := by
        have := Nat.mul_le_mul_left m (show i + 1 ≤ n from hi2)
        rw [Nat.mul_add, Nat.mul_one] at this
        exact this
      have hn1 : n * j + n ≤ n * m := by
        have := Nat.mul_le_mul_left n (show j + 1 ≤ m from hj2)
        rw [Nat.mul_add, Nat.mul_one] at this
        exact this
      have hc2 : 2 * (j + m * i) + 1 < 2 * (m * n) := by omega
      have hw2 : 2 * (i + n * j) + 1 < 2 * (n * m) := by omega
      -- the input entry $(j, i)$ read off the stored matrix
      have ea : t₁.store.read p X (xo.eval + 2 * (j + m * i)) =
          some (A ⟨j, hj2⟩ ⟨i, hi2⟩).1 := by
        rw [hOUT' p X _ (hXout _ (by omega) (by omega))]
        exact (hXw j hj2 i hi2).1
      have ea' : a = (A ⟨j, hj2⟩ ⟨i, hi2⟩).1 := Option.some.inj (ha.symm.trans ea)
      have eb : u.read p X (xo.eval + 2 * (j + m * i) + 1) = some (A ⟨j, hj2⟩ ⟨i, hi2⟩).2 := by
        rw [Store.read_of_write_eq_some_of_ne hu
          (hsep _ _ (by omega) (by omega) (by omega) (by omega)), hOUT' p X _ (hXout _ (by omega) (by omega))]
        exact (hXw j hj2 i hi2).2
      have eb' : b = (A ⟨j, hj2⟩ ⟨i, hi2⟩).2 := Option.some.inj (hb.symm.trans eb)
      -- the cells written by this step
      have r1 : t₂.store.read p Y (yo.eval + 2 * (i + n * j)) = some a := by
        rw [hs2, Store.read_of_write_eq_some_of_ne hu' (Or.inr (show yo.eval + 2 * (i + n * j) ≠
          yo.eval + 2 * (i + n * j) + 1 by omega) : Y ≠ Y ∨ _)]
        exact Store.read_of_write_eq_some hu
      have r2 : t₂.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some ((M.neg b)) := by
        rw [hs2]
        exact Store.read_of_write_eq_some hu'
      refine ⟨fun i' j' hlt => ?_, fun q c d hd => ?_, ?_, ?_⟩
      · rcases Nat.lt_or_ge ((i' : ℕ) + n * (j' : ℕ)) (n * j + i) with hl | hge
        · obtain ⟨g1, g2⟩ := hG' i' j' hl
          constructor
          · rw [hs2, Store.read_of_write_eq_some_of_ne hu' (Or.inr (show
              yo.eval + 2 * ((i' : ℕ) + n * (j' : ℕ)) ≠ yo.eval + 2 * (i + n * j) + 1 by omega) :
              Y ≠ Y ∨ _), Store.read_of_write_eq_some_of_ne hu (Or.inr (show
              yo.eval + 2 * ((i' : ℕ) + n * (j' : ℕ)) ≠ yo.eval + 2 * (i + n * j) by omega) :
              Y ≠ Y ∨ _)]
            exact g1
          · rw [hs2, Store.read_of_write_eq_some_of_ne hu' (Or.inr (show
              yo.eval + 2 * ((i' : ℕ) + n * (j' : ℕ)) + 1 ≠ yo.eval + 2 * (i + n * j) + 1 by omega) :
              Y ≠ Y ∨ _), Store.read_of_write_eq_some_of_ne hu (Or.inr (show
              yo.eval + 2 * ((i' : ℕ) + n * (j' : ℕ)) + 1 ≠ yo.eval + 2 * (i + n * j) by omega) :
              Y ≠ Y ∨ _)]
            exact g2
        · obtain ⟨e1, e2⟩ := hinj i (i' : ℕ) j (j' : ℕ) hi2 i'.isLt (by omega)
          have hi'eq : i' = ⟨i, hi2⟩ := Fin.ext e1.symm
          have hj'eq : j' = ⟨j, hj2⟩ := Fin.ext e2.symm
          subst hi'eq hj'eq
          exact ⟨r1.trans (congrArg some ea'), r2.trans (congrArg some (congrArg M.neg eb'))⟩
      · rw [hs2, Store.read_of_write_eq_some_of_ne hu' (hne_of _ _ (yo.eval + 2 * (i + n * j) + 1)
          hd (by omega) (by omega)), Store.read_of_write_eq_some_of_ne hu
          (hne_of _ _ (yo.eval + 2 * (i + n * j)) hd (by omega) (by omega)), hOUT' q c d hd]
      · rw [hs2, Store.shape_of_write_eq_some hu', Store.shape_of_write_eq_some hu, hsh']
      · rw [hp2, hpos']
    obtain ⟨hG'', hOUT'', hsh'', hpos''⟩ := inner
    refine ⟨fun i' j' hlt => hG'' i' j' ?_, fun q b c hd => hOUT'' q b c hd,
      hsh''.trans hsh, hpos''.trans hpos⟩
    have e : n * (j + 1) = n * j + n := by ring
    have hn : (IExp.const n).eval = n := rfl
    omega
  obtain ⟨hG, hOUT, -, -⟩ := inv
  refine ⟨fun i j (t : Fin 2) => ?_, hOUT⟩
  have hij : (i : ℕ) + n * (j : ℕ) < n * m := by
    have e := Nat.mul_le_mul_left n (show (j : ℕ) + 1 ≤ m from j.isLt)
    rw [Nat.mul_add, Nat.mul_one] at e
    have := i.isLt
    omega
  obtain ⟨g1, g2⟩ := hG i j hij
  fin_cases t
  · simpa [pairLayout] using g1
  · simpa [pairLayout, Nat.add_assoc] using g2

/-- **`ztraceRe` computes the machine's real trace**: a successful run of
`NLAlib.Computation.ztraceRe` from a block at `X` holding the complex $n \times n$ matrix
$\mathbf{A}$, into a cell outside it, ends with the cell holding `M.traceRe A`, every other cell
unchanged. No printed source.
Proof: after the literal $0$, the loop keeps "the cell holds the left fold over the first $i$
diagonal real parts" (`NLAlib.Computation.forall_of_exec_loop_eq_some`, scaffold);
`List.finRange_succ_last`-style `List.foldl_append` matches `NLAlib.FloatMachine.traceRe`. M,
about 30 lines. -/
theorem read_of_exec_ztraceRe (p : P) (n : ℕ) {X : ℕ} {xo : IExp ℕ} {dst : Cell ℕ ℕ}
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hdX : blockDisjoint (dst.buf, dst.idx.eval, 1) (X, xo.eval, 2 * (n * n)) = true)
    (h : exec I (ztraceRe (ι := ι) p (.const n) X xo dst).run st = some st') :
    st'.store.read p dst.buf dst.idx.eval =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).traceRe A) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (dst.buf, dst.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal with hM
  have key : (ztraceRe (ι := ι) p (.const n) X xo dst).run = .seq
      (.named "ztraceRe" [.idx (.const n), .buf X, .idx xo, .cell dst]
        (.seq (.instr (.lit p dst 0)) (.seq (.loop (IExp.const n) fun i => .seq
          (.instr (.bin p .add dst dst ⟨X, xo + zidx (IExp.const n) (.var i) (.var i)⟩)) .skip)
          .skip)))
      .skip := rfl
  rw [key, exec_seq_skip, exec_named] at h
  -- the literal $0$ first
  obtain ⟨v0, hv0⟩ : ∃ v, I.sem.lit p 0 = some v := by
    cases hl : I.sem.lit p 0 with
    | none => simp [exec_seq, exec_instr, Instr.run, hl] at h
    | some v => exact ⟨v, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s, st.store.write p dst.buf dst.idx.eval v0 = some s := by
    cases hw : st.store.write p dst.buf dst.idx.eval v0 with
    | none => simp [exec_seq, exec_instr, Instr.run, hv0, hw] at h
    | some s => exact ⟨s, rfl⟩
  rw [exec_seq_instr_lit I hv0 hs0, exec_seq_skip] at h
  have hMz : M.zero = v0 := by
    show (I.sem.lit p 0).getD default = v0
    rw [hv0]; rfl
  -- the cells of the input block read as stored
  have hXd : ∀ i (hi : i < n), st.store.read p X (xo.eval + 2 * (i + n * i)) =
      some (A ⟨i, hi⟩ ⟨i, hi⟩).1 := by
    intro i hi
    simpa [pairLayout] using hA ⟨i, hi⟩ ⟨i, hi⟩ (0 : Fin 2)
  have hdis : ∀ i (hi : i < n), blockDisjoint (X, xo.eval + 2 * (i + n * i), 1)
      (dst.buf, dst.idx.eval, 1) = true := by
    intro i hi
    have hlt : i + n * i < n * n := by nlinarith [Nat.mul_le_mul_left n (show i + 1 ≤ n from hi)]
    by_cases hb : dst.buf = X
    · rw [hb] at hdX ⊢
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
        Bool.or_eq_true] at hdX ⊢
      omega
    · simp [blockDisjoint, Ne.symm hb]
  -- one step: the accumulator plus the diagonal real part
  have bstep : ∀ (k : ℕ) (acc : K) (s₁ s₂ : St P K C),
      s₁.store.read p dst.buf dst.idx.eval = some acc →
      exec I (.seq (.instr (.bin p .add dst dst ⟨X, xo + zidx (IExp.const n) (.var k) (.var k)⟩))
        .skip) s₁ = some s₂ →
      ∃ x s, s₁.store.read p X (xo.eval + 2 * (k + n * k)) = some x ∧
        s₁.store.write p dst.buf dst.idx.eval (M.add acc x) = some s ∧
        s₂.store = s ∧ s₂.pos = s₁.pos := by
    intro k acc s₁ s₂ hacc hr
    obtain ⟨x, hx⟩ : ∃ x, s₁.store.read p X (xo.eval + 2 * (k + n * k)) = some x := by
      cases hx : s₁.store.read p X (xo.eval + 2 * (k + n * k)) with
      | none => simp [exec_seq, exec_instr, Instr.run, hacc, hx, zidx, IExp.eval] at hr
      | some x => exact ⟨x, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, I.sem.bin p .add acc x = some v := by
      cases hb : I.sem.bin p .add acc x with
      | none => simp [exec_seq, exec_instr, Instr.run, hacc, hx, hb, zidx, IExp.eval] at hr
      | some v => exact ⟨v, rfl⟩
    obtain ⟨s, hw⟩ : ∃ s, s₁.store.write p dst.buf dst.idx.eval v = some s := by
      cases hw : s₁.store.write p dst.buf dst.idx.eval v with
      | none => simp [exec_seq, exec_instr, Instr.run, hacc, hx, hv, hw, zidx, IExp.eval] at hr
      | some s => exact ⟨s, rfl⟩
    have hMv : M.add acc x = v := by
      show (I.sem.bin p .add acc x).getD default = v
      rw [hv]; rfl
    rw [exec_seq_instr_bin (dst := dst) (x := dst) (y := (⟨X, xo + zidx (IExp.const n) (IExp.var k) (IExp.var k)⟩ : Cell ℕ ℕ)) I hacc hx hv hw, exec_skip] at hr
    cases hr
    exact ⟨x, s, hx, hMv ▸ hw, rfl, rfl⟩
  -- the fold over the first $k + 1$ diagonal entries is one more step
  have hfold : ∀ k (hk : k < n), ((List.finRange n).take (k + 1)).foldl
      (fun acc j => M.add acc (A j j).1) M.zero =
      M.add (((List.finRange n).take k).foldl (fun acc j => M.add acc (A j j).1) M.zero)
        (A ⟨k, hk⟩ ⟨k, hk⟩).1 := by
    intro k hk
    rw [List.take_succ, List.foldl_append]
    simp [hk]
  have hne_of : ∀ b j, blockDisjoint (b, j, 1) (dst.buf, dst.idx.eval, 1) = true →
      b ≠ dst.buf ∨ j ≠ dst.idx.eval := by
    intro b j hd
    by_cases hb : b = dst.buf
    · right
      rw [hb] at hd
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
        Bool.or_eq_true] at hd
      omega
    · exact Or.inl hb
  -- the loop keeps the fold of the first $k$ diagonal real parts in the cell `dst`
  have inv := forall_of_exec_loop_eq_some (I := I) (fun k s =>
      s.store.read p dst.buf dst.idx.eval = some (((List.finRange n).take k).foldl
        (fun acc j => M.add acc (A j j).1) M.zero) ∧
      (∀ q b j, blockDisjoint (b, j, 1) (dst.buf, dst.idx.eval, 1) = true →
        s.store.read q b j = st.store.read q b j) ∧
      s.store.shape = st.store.shape ∧ s.pos = st.pos) ?_ ?_ h
  rotate_left
  · refine ⟨?_, fun q b j hd => Store.read_of_write_eq_some_of_ne hs0 (hne_of b j hd),
      Store.shape_of_write_eq_some hs0, rfl⟩
    rw [List.take_zero, List.foldl_nil, hMz]
    exact Store.read_of_write_eq_some hs0
  · intro k hk s₁ s₂ ⟨hd, hout, hsh, hpos⟩ hr
    have hk2 : k < n := hk
    obtain ⟨x, s, hx, hw, hs, hp⟩ := bstep k _ s₁ s₂ hd hr
    rw [hout _ _ _ (hdis k hk2), hXd k hk2] at hx
    have hxA : x = (A ⟨k, hk2⟩ ⟨k, hk2⟩).1 := (Option.some.inj hx).symm
    refine ⟨?_, fun q b j hdj => ?_, ?_, ?_⟩
    · rw [hs, Store.read_of_write_eq_some hw, hfold k hk2, hxA]
    · rw [hs, Store.read_of_write_eq_some_of_ne hw (hne_of b j hdj)]
      exact hout q b j hdj
    · rw [hs, Store.shape_of_write_eq_some hw, hsh]
    · rw [hp, hpos]
  obtain ⟨hdst, hout, -, -⟩ := inv
  rw [List.take_of_length_le (by simp)] at hdst
  exact ⟨hdst, hout⟩

end NLAlib.Computation
