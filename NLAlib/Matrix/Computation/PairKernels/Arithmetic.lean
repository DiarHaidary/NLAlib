/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PairKernels.Hermitian

/-!
# Complex-pair kernels: identity, sums, scaling, conjugate transpose, trace

The rounded specifications of the complex kernels that the sign and deflation programs do not call:
the identity, the sum and difference of two blocks, scaling by a stored scalar, the conjugate
transpose and the real part of the trace. A successful run writes the result of the corresponding
operation of the machine of the semantics.

## Main results

* `NLAlib.Computation.holds_of_exec_zidentity`, `NLAlib.Computation.holds_of_exec_zadd`,
  `NLAlib.Computation.holds_of_exec_zsub`, `NLAlib.Computation.holds_of_exec_zscal`,
  `NLAlib.Computation.holds_of_exec_zconjTranspose`, `NLAlib.Computation.read_of_exec_ztraceRe`:
  what a successful run computes.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### Kernels for later stages: identity, sums, scaling, conjugate transpose, trace -/

/-- `zidentity` writes the stored identity: a successful run of
`NLAlib.Computation.zidentity` ends with the block at `Y` holding the machine's identity matrix
(`NLAlib.FloatMachine.identityMat`), every cell outside it unchanged. No printed source. -/
theorem holds_of_exec_zidentity (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st st' : St P K C}
    (h : exec I (zidentity (ι := ι) p (.const n) Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).identityMat n) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  set M := I.sem.toFloatMachine p toNat mmR qrR unif normal
  have hrun : (zidentity (ι := ι) p (.const n) Y yo).run = .seq (.named "zidentity"
      [.idx (.const n), .buf Y, .idx yo]
      (.seq (.loop (2 * (.const n * .const n)) fun w =>
          .seq (.instr (.lit p ⟨Y, yo + .var w⟩ 0)) .skip)
        (.seq (.loop (.const n) fun i =>
          .seq (.instr (.lit p ⟨Y, yo + zidx (.const n) (.var i) (.var i)⟩ 1)) .skip) .skip)))
      .skip := rfl
  rw [hrun, exec_seq_skip, exec_named, exec_seq, Option.bind_eq_some_iff] at h
  obtain ⟨σ, h₁, h₂⟩ := h
  rw [exec_seq_skip] at h₂
  have hN : (2 * (IExp.const n * IExp.const n)).eval = 2 * (n * n) := by
    simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
  -- the zero loop
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I
    (fun w s => (∀ k < w, s.store.read p Y (yo.eval + k) = some M.zero) ∧
      ∀ q b i, (b ≠ Y ∨ i < yo.eval ∨ yo.eval + w ≤ i) →
        s.store.read q b i = st.store.read q b i)
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h₁)
  · rw [hN] at hR
    obtain ⟨hZ, hfr⟩ := hR
    -- the diagonal loop
    let D : ℕ → ℕ → Prop := fun i k => ∃ d < i, k = 2 * (d + n * d)
    refine (fun hR => ?_) (forall_of_exec_loop_eq_some I
      (fun i s => (∀ k < 2 * (n * n), (D i k → s.store.read p Y (yo.eval + k) = some M.one) ∧
          (¬ D i k → s.store.read p Y (yo.eval + k) = some M.zero)) ∧
        ∀ q b j, (b ≠ Y ∨ j < yo.eval ∨ yo.eval + 2 * (n * n) ≤ j) →
          s.store.read q b j = st.store.read q b j)
      ⟨fun k hk => ⟨fun ⟨_, hd, _⟩ => absurd hd (Nat.not_lt_zero _), fun _ => hZ k hk⟩, hfr⟩
      ?_ h₂)
    · obtain ⟨hI, hfr'⟩ := hR
      simp only [IExp.eval_const] at hI
      refine ⟨fun a b t => ?_, fun q c k hk => hfr' q c k ?_⟩
      · obtain ⟨t, ht⟩ := t
        change t < 2 at ht
        have hk : 2 * (a.1 + n * b.1) + t < 2 * (n * n) := by
          have := zherm_lt a.2 b.2; omega
        change st'.store.read p Y (yo.eval + (2 * (a.1 + n * b.1) + t)) = some (pairLayout.put _ _)
        by_cases hab : a = b ∧ t = 0
        · obtain ⟨rfl, rfl⟩ := hab
          rw [(hI _ hk).1 ⟨a.1, a.2, rfl⟩]
          simp only [FloatMachine.identityMat, Matrix.of_apply, if_true]
          rfl
        · rw [(hI _ hk).2 ?_]
          · rcases t with _ | _ | t
            · simp only [FloatMachine.identityMat, Matrix.of_apply]
              split_ifs with he
              · exact absurd ⟨he, rfl⟩ hab
              · rfl
            · simp only [FloatMachine.identityMat, Matrix.of_apply]
              split_ifs <;> rfl
            · omega
          · rintro ⟨d, hd, he⟩
            have ht0 : t = 0 := by omega
            subst ht0
            have := zmirror_index_inj a.2 hd (show a.1 + n * b.1 = d + n * d by omega)
            exact hab ⟨Fin.ext (this.1.trans this.2.symm), rfl⟩
      · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hk
        by_cases hcY : c = Y
        · exact Or.inr (by omega)
        · exact Or.inl hcY
    rintro i hi s₁ s₂ ⟨hI, hfr₁⟩ hex
    simp only [IExp.eval_const] at hi
    rw [exec_seq_skip, exec_instr] at hex
    simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
    obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
    simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
      IExp.eval_ofNat] at hw'
    have hik := zherm_lt hi hi
    have hv' : M.one = v := by
      have hv' : I.sem.lit p 1 = some v := by exact_mod_cast hv
      simp only [M, ScalarSem.toFloatMachine, hv', Option.getD_some]
    refine ⟨fun k hk => ?_, fun q b j hb => (Store.read_of_write_eq_some_of_ne hw' ?_).trans
      (hfr₁ q b j hb)⟩
    · by_cases hki : k = 2 * (i + n * i)
      · subst hki
        refine ⟨fun _ => (Store.read_of_write_eq_some hw').trans (congrArg some hv'.symm),
          fun hD => absurd ⟨i, Nat.lt_succ_self _, rfl⟩ hD⟩
      · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega))]
        have hD : D (i + 1) k ↔ D i k := by
          constructor
          · rintro ⟨d, hd, he⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | rfl
            · exact ⟨d, hd, he⟩
            · exact absurd he hki
          · rintro ⟨d, hd, he⟩
            exact ⟨d, Nat.lt_succ_of_lt hd, he⟩
        rw [hD]
        exact hI k hk
    · rcases hb with hb | hb
      · exact Or.inl hb
      · exact Or.inr (by omega)
  rintro w hw s₁ s₂ ⟨hY, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  simp only [IExp.eval_add, IExp.eval_var] at hw'
  refine ⟨fun k hk => ?_,
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

/-- `zadd` adds the parts: a successful run of `NLAlib.Computation.zadd` from blocks at `X`,
`Y` holding $\mathbf{A}$, $\mathbf{B}$, into a block at `Z` disjoint from both or equal to one of
them, ends with the block at `Z` holding the entrywise machine sums of the real and of the
imaginary parts, every cell outside it unchanged. No printed source. -/
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

/-- `zsub` subtracts the parts: as `NLAlib.Computation.holds_of_exec_zadd`, with the
machine's subtraction. No printed source. -/
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

/-- `zscal` scales the parts: a successful run of `NLAlib.Computation.zscal` from a block at
`X` holding $\mathbf{A}$ and a cell `a` holding $a$, into a block at `Y` disjoint from `a` and
disjoint from or equal to the block at `X`, ends with the block at `Y` holding the entrywise
machine products of $a$ with both parts, every cell outside it unchanged. No printed source. -/
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

/-- `zconjTranspose` computes the machine's conjugate transpose: a successful run of
`NLAlib.Computation.zconjTranspose` from a block at `X` holding the complex $m \times n$ matrix
$\mathbf{A}$, into a block at `Y` disjoint from it, ends with the block at `Y` holding
`M.conjTransposeMat A`, every cell outside it unchanged. No printed source. -/
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

/-- `ztraceRe` computes the machine's real trace: a successful run of
`NLAlib.Computation.ztraceRe` from a block at `X` holding the complex $n \times n$ matrix
$\mathbf{A}$, into a cell outside it, ends with the cell holding `M.traceRe A`, every other cell
unchanged. No printed source. -/
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
