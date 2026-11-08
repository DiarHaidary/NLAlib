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

/-- The loop of a constant fill: a successful run of the loop that writes the literal $q$ into
the cells `yo + w`, $w < N$, of the block at `Y` ends with each of them holding the literal, every
other cell unchanged (`NLAlib.Computation.read_of_exec_loop_lit` at contiguous cells). -/
private theorem forall_read_of_exec_loop_lit {p : P} {q : ℚ} {N Y : ℕ} {yo e : IExp ℕ}
    {st st' : St P K C} (hN : e.eval = N)
    (h : exec I (.loop e fun w => .seq (.instr (.lit p ⟨Y, yo + .var w⟩ q)) .skip) st = some st') :
    (∀ k < N, st'.store.read p Y (yo.eval + k) = some ((I.sem.lit p q).getD default)) ∧
      ∀ q' c i, (c ≠ Y ∨ i < yo.eval ∨ yo.eval + N ≤ i) →
        st'.store.read q' c i = st.store.read q' c i := by
  subst hN
  obtain ⟨-, -, hR, hfr⟩ := read_of_exec_loop_lit h
  refine ⟨fun k hk => ?_, fun q' c i hc => hfr q' c i (hc.imp_right fun hi w hw => ?_)⟩
  · obtain ⟨z, hz, hr⟩ := hR k hk
    simpa only [IExp.eval_add, IExp.eval_var, hz, Option.getD_some] using hr
  · simp only [IExp.eval_add, IExp.eval_var]
    omega

/-- The diagonal loop of `zidentity`: from a block at `Y` holding $z$ in every word, a successful
run of the loop that writes the literal $1$ into the real part of each diagonal entry ends with
the block holding $1$ there and $z$ elsewhere, every cell outside the block unchanged. -/
private theorem read_of_exec_loop_lit_diag {p : P} {n Y : ℕ} {yo : IExp ℕ} {z : K}
    {st st' : St P K C} (hZ : ∀ k < 2 * (n * n), st.store.read p Y (yo.eval + k) = some z)
    (h : exec I (.loop (.const n) fun i =>
      .seq (.instr (.lit p ⟨Y, yo + zidx (.const n) (.var i) (.var i)⟩ 1)) .skip) st = some st') :
    (∀ k < 2 * (n * n),
      ((∃ d < n, k = 2 * (d + n * d)) →
        st'.store.read p Y (yo.eval + k) = some ((I.sem.lit p 1).getD default)) ∧
      (¬ (∃ d < n, k = 2 * (d + n * d)) → st'.store.read p Y (yo.eval + k) = some z)) ∧
      ∀ q c j, (c ≠ Y ∨ j < yo.eval ∨ yo.eval + 2 * (n * n) ≤ j) →
        st'.store.read q c j = st.store.read q c j := by
  refine forall_of_exec_loop_eq_some I (fun i s =>
    (∀ k < 2 * (n * n),
      ((∃ d < i, k = 2 * (d + n * d)) →
        s.store.read p Y (yo.eval + k) = some ((I.sem.lit p 1).getD default)) ∧
      (¬ (∃ d < i, k = 2 * (d + n * d)) → s.store.read p Y (yo.eval + k) = some z)) ∧
      ∀ q c j, (c ≠ Y ∨ j < yo.eval ∨ yo.eval + 2 * (n * n) ≤ j) →
        s.store.read q c j = st.store.read q c j)
    ⟨fun k hk => ⟨fun ⟨_, hd, _⟩ => absurd hd (Nat.not_lt_zero _), fun _ => hZ k hk⟩,
      fun _ _ _ _ => rfl⟩ ?_ h
  rintro i hi s₁ s₂ ⟨hD, hfr⟩ hex
  change i < n at hi
  obtain ⟨v, s', hv, hw', hex⟩ := exists_of_exec_seq_lit hex
  rw [exec_skip, Option.some_inj] at hex
  subst hex
  simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
    IExp.eval_ofNat] at hw'
  have := Nat.add_mul_lt_mul_of_lt_of_lt hi hi
  refine ⟨fun k hk => ?_, fun q c j hc =>
    (Store.read_of_write_eq_some_of_ne hw' (by omega)).trans (hfr q c j hc)⟩
  by_cases hki : k = 2 * (i + n * i)
  · subst hki
    refine ⟨fun _ => ?_, fun hD => absurd ⟨i, Nat.lt_succ_self _, rfl⟩ hD⟩
    rw [Store.read_of_write_eq_some hw', hv, Option.getD_some]
  · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega))]
    have hD' : (∃ d < i + 1, k = 2 * (d + n * d)) ↔ ∃ d < i, k = 2 * (d + n * d) := by
      refine ⟨fun ⟨d, hd, he⟩ => ⟨d, ?_, he⟩, fun ⟨d, hd, he⟩ => ⟨d, Nat.lt_succ_of_lt hd, he⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | rfl
      · exact hd
      · exact absurd he hki
    rw [hD']
    exact hD k hk

/-- `zidentity` writes the stored identity: a successful run of
`NLAlib.Computation.zidentity` ends with the block at `Y` holding the machine's identity matrix
(`NLAlib.FloatMachine.identityMat`), every cell outside it unchanged. No printed source. -/
theorem holds_of_exec_zidentity (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st st' : St P K C}
    (h : exec I (zidentity (ι := ι) p (.const n) Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).identityMat n) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  change exec I (.seq (.named _ _ (.seq (.loop _ fun w => .seq (.instr (.lit p ⟨Y, yo + .var w⟩ 0))
    .skip) (.seq (.loop _ fun i => .seq (.instr (.lit p ⟨Y, yo + zidx (.const n) (.var i)
    (.var i)⟩ 1)) .skip) .skip))) .skip) st = some st' at h
  rw [exec_seq_skip, exec_named, exec_seq, Option.bind_eq_some_iff] at h
  obtain ⟨σ, h₁, h₂⟩ := h
  rw [exec_seq_skip] at h₂
  obtain ⟨hZ, hfr⟩ := forall_read_of_exec_loop_lit (N := 2 * (n * n)) (by simp) h₁
  obtain ⟨hI, hfr'⟩ := read_of_exec_loop_lit_diag hZ h₂
  refine ⟨fun a b ⟨t, ht⟩ => ?_, fun q c k hk => ?_⟩
  swap
  · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hk
    exact (hfr' q c k (by omega)).trans (hfr q c k (by omega))
  change t < 2 at ht
  have := Nat.add_mul_lt_mul_of_lt_of_lt a.2 b.2
  have hk : 2 * (a.1 + n * b.1) + t < 2 * (n * n) := by omega
  change st'.store.read p Y (yo.eval + (2 * (a.1 + n * b.1) + t)) = some (pairLayout.put _ _)
  by_cases hab : a = b ∧ t = 0
  · obtain ⟨rfl, rfl⟩ := hab
    rw [(hI _ hk).1 ⟨a.1, a.2, rfl⟩]
    simp only [FloatMachine.identityMat, Matrix.of_apply, if_true]
    rfl
  rw [(hI _ hk).2 ?_]
  · rcases t with _ | _ | t
    · simp only [FloatMachine.identityMat, Matrix.of_apply]
      split_ifs with he
      · exact absurd ⟨he, rfl⟩ hab
      · rfl
    · simp only [FloatMachine.identityMat, Matrix.of_apply]
      split_ifs <;> rfl
    · omega
  rintro ⟨d, hd, he⟩
  obtain rfl : t = 0 := by omega
  have := (Nat.add_mul_eq_add_mul_iff_of_lt a.2 hd).1 (show a.1 + n * b.1 = d + n * d by omega)
  exact hab ⟨Fin.ext (this.1.trans this.2.symm), rfl⟩

/-- The loop of an entrywise kernel: a successful run of the loop that writes, for each $w < N$,
the operation `b` of the cells `x w` and `y w` into the cell `zo + w` of the block at `Z`, where
no operand cell is written before it is read, ends with every cell `zo + w` holding the
operation of the operands as stored at the start, every cell outside the block unchanged. -/
private theorem read_of_exec_loop_bin {p : P} {b : BinOp} {N Z : ℕ} {zo e : IExp ℕ}
    {x y : ℕ → Cell ℕ ℕ} {st st' : St P K C} (hN : e.eval = N)
    (hx : ∀ w < N, (x w).buf ≠ Z ∨ (x w).idx.eval < zo.eval ∨ zo.eval + w ≤ (x w).idx.eval)
    (hy : ∀ w < N, (y w).buf ≠ Z ∨ (y w).idx.eval < zo.eval ∨ zo.eval + w ≤ (y w).idx.eval)
    (h : exec I (.loop e fun w =>
      .seq (.instr (.bin p b ⟨Z, zo + .var w⟩ (x w) (y w))) .skip) st = some st') :
    (∀ k < N, st'.store.read p Z (zo.eval + k) =
      (st.store.read p (x k).buf (x k).idx.eval).bind fun a =>
        (st.store.read p (y k).buf (y k).idx.eval).map fun c => (I.sem.bin p b a c).getD default) ∧
      ∀ q c i, blockDisjoint (c, i, 1) (Z, zo.eval, N) = true →
        st'.store.read q c i = st.store.read q c i := by
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I (fun w s =>
    (∀ k < w, s.store.read p Z (zo.eval + k) =
      (st.store.read p (x k).buf (x k).idx.eval).bind fun a =>
        (st.store.read p (y k).buf (y k).idx.eval).map fun c => (I.sem.bin p b a c).getD default) ∧
      ∀ q c i, (c ≠ Z ∨ i < zo.eval ∨ zo.eval + w ≤ i) →
        s.store.read q c i = st.store.read q c i)
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h)
  · rw [hN] at hR
    refine ⟨hR.1, fun q c i hc => hR.2 q c i ?_⟩
    simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hc
    omega
  rintro w hw s₁ s₂ ⟨hZ, hfr⟩ hex
  rw [hN] at hw
  obtain ⟨a, c, v, s', ha, hc, hv, hw', hex⟩ := exists_of_exec_seq_bin hex
  rw [exec_skip, Option.some_inj] at hex
  subst hex
  simp only [IExp.eval_add, IExp.eval_var] at hw'
  refine ⟨fun k hk => ?_,
    fun q c i hc => (Store.read_of_write_eq_some_of_ne hw' (by omega)).trans (hfr q c i (by omega))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
  · exact (Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega))).trans (hZ k hk)
  · rw [Store.read_of_write_eq_some hw', ← hfr _ _ _ (hx k hw), ha, Option.bind_some,
      ← hfr _ _ _ (hy k hw), hc, Option.map_some, hv, Option.getD_some]

omit [DecidableEq P] [Inhabited K] in
/-- An operand block disjoint from or equal to the output block at `Z` is never written before it
is read. -/
private theorem operand_of_blockDisjoint_or_eq {Z W N : ℕ} {zo wo : IExp ℕ}
    (hW : blockDisjoint (Z, zo.eval, N) (W, wo.eval, N) = true ∨ (Z = W ∧ zo.eval = wo.eval)) :
    ∀ w < N, W ≠ Z ∨ wo.eval + w < zo.eval ∨ zo.eval + w ≤ wo.eval + w := by
  intro w hw
  rcases hW with hW | ⟨rfl, he⟩
  · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hW
    omega
  · omega

omit [Inhabited K] in
/-- The entrywise operation `op` of two stored complex $m \times n$ matrices, part by part, is
stored at `Z` when every word of the block at `Z` holds `op` of the words of the blocks. -/
private theorem holds_of_forall_read_eq_bind {p : P} {m n X Y Z xo yo zo : ℕ}
    {st s : Store P K} {A B : Matrix (Fin m) (Fin n) (K × K)} (op : K → K → K)
    (hA : pairLayout.Holds st p X xo A) (hB : pairLayout.Holds st p Y yo B)
    (hZ : ∀ k < 2 * (m * n), s.read p Z (zo + k) =
      (st.read p X (xo + k)).bind fun a => (st.read p Y (yo + k)).map (op a)) :
    pairLayout.Holds s p Z zo
      (Matrix.of fun i j => (op (A i j).1 (B i j).1, op (A i j).2 (B i j).2)) := by
  intro i j ⟨t, ht⟩
  change t < 2 at ht
  have := Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2
  change s.read p Z (zo + (2 * (i.1 + m * j.1) + t)) = _
  rw [hZ (2 * (i.1 + m * j.1) + t) (by omega),
    show st.read p X (xo + (2 * (i.1 + m * j.1) + t)) = _ from hA i j ⟨t, ht⟩,
    show st.read p Y (yo + (2 * (i.1 + m * j.1) + t)) = _ from hB i j ⟨t, ht⟩, Option.bind_some,
    Option.map_some]
  rcases t with _ | _ | t
  · rfl
  · rfl
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
  change exec I (.seq (.named _ _ (.seq (.loop _ fun w => .seq (.instr (.bin p .add
    ⟨Z, zo + .var w⟩ ⟨X, xo + .var w⟩ ⟨Y, yo + .var w⟩)) .skip) .skip)) .skip) st = some st' at h
  rw [exec_seq_skip, exec_named, exec_seq_skip] at h
  obtain ⟨hZ, hfr⟩ := read_of_exec_loop_bin (by simp) (operand_of_blockDisjoint_or_eq hZX)
    (operand_of_blockDisjoint_or_eq hZY) h
  exact ⟨holds_of_forall_read_eq_bind _ hA hB hZ, hfr⟩

/-- `zsub` subtracts the parts: a successful run of `NLAlib.Computation.zsub` from blocks at
`X`, `Y` holding $\mathbf{A}$, $\mathbf{B}$, into a block at `Z` disjoint from both or equal to one
of them, ends with the block at `Z` holding the entrywise machine differences of the real and of
the imaginary parts, every cell outside it unchanged. No printed source. -/
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
  change exec I (.seq (.named _ _ (.seq (.loop _ fun w => .seq (.instr (.bin p .sub
    ⟨Z, zo + .var w⟩ ⟨X, xo + .var w⟩ ⟨Y, yo + .var w⟩)) .skip) .skip)) .skip) st = some st' at h
  rw [exec_seq_skip, exec_named, exec_seq_skip] at h
  obtain ⟨hZ, hfr⟩ := read_of_exec_loop_bin (by simp) (operand_of_blockDisjoint_or_eq hZX)
    (operand_of_blockDisjoint_or_eq hZY) h
  exact ⟨holds_of_forall_read_eq_bind _ hA hB hZ, hfr⟩

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
  change exec I (.seq (.named _ _ (.seq (.loop _ fun w => .seq (.instr (.bin p .mul
    ⟨Y, yo + .var w⟩ a ⟨X, xo + .var w⟩)) .skip) .skip)) .skip) st = some st' at h
  rw [exec_seq_skip, exec_named, exec_seq_skip] at h
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at haY
  obtain ⟨hY, hfr⟩ := read_of_exec_loop_bin (x := fun _ => a) (by simp) (fun w hw => by omega)
    (operand_of_blockDisjoint_or_eq hXY) h
  simp only [IExp.eval_add, IExp.eval_var] at hY
  refine ⟨fun i j ⟨t, ht⟩ => ?_, hfr⟩
  change t < 2 at ht
  have := Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2
  change st'.store.read p Y (yo.eval + (2 * (i.1 + m * j.1) + t)) = _
  rw [hY (2 * (i.1 + m * j.1) + t) (by omega), ha, Option.bind_some,
    show st.store.read p X (xo.eval + (2 * (i.1 + m * j.1) + t)) = _ from hA i j ⟨t, ht⟩,
    Option.map_some]
  rcases t with _ | _ | t
  · rfl
  · rfl
  · omega

/-- The invariant of the loops of `zconjTranspose`: every entry of $\mathbf{B}$ of flat index
below $k$ stored in the block at `Y`, every cell outside it as in `st`. -/
private def ZConjInv (p : P) (n m Y yo : ℕ) (st : St P K C) (B : Matrix (Fin n) (Fin m) (K × K))
    (k : ℕ) (s : St P K C) : Prop :=
  (∀ (i : Fin n) (j : Fin m), (i : ℕ) + n * j < k →
    s.store.read p Y (yo + 2 * (i + n * j)) = some (B i j).1 ∧
      s.store.read p Y (yo + 2 * (i + n * j) + 1) = some (B i j).2) ∧
    ∀ q b c, blockDisjoint (b, c, 1) (Y, yo, 2 * (n * m)) = true →
      s.store.read q b c = st.store.read q b c

/-- One entry of `zconjTranspose`: the copy of the real part of entry $(j, i)$ of $\mathbf{A}$ and
its negated imaginary part into entry $(i, j)$ of the output extend the invariant by one flat
index. -/
private theorem ZConjInv.step {p : P} {m n X Y : ℕ} {xo yo : IExp ℕ} {st t₁ t₂ : St P K C}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * m)) (X, xo.eval, 2 * (m * n)) = true)
    {i j : ℕ} (hi : i < n) (hj : j < m)
    (hI : ZConjInv p n m Y yo.eval st
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).conjTransposeMat A) (n * j + i) t₁)
    (h : exec I (.seq (.instr (.copy p ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
        ⟨X, xo + zidx (.const m) (.var j) (.var i)⟩))
      (.seq (.instr (.un p .neg ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
        ⟨X, xo + zidx (.const m) (.var j) (.var i) + 1⟩)) .skip)) t₁ = some t₂) :
    ZConjInv p n m Y yo.eval st
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).conjTransposeMat A) (n * j + i + 1)
      t₂ := by
  unfold ZConjInv at hI ⊢
  obtain ⟨hD, hfr⟩ := hI
  obtain ⟨a, u, ha, hu, h⟩ := exists_of_exec_seq_copy h
  obtain ⟨b, v, u', hb, hv, hu', h⟩ := exists_of_exec_seq_un h
  rw [exec_skip, Option.some_inj] at h
  subst h
  simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
    IExp.eval_ofNat] at ha hu hb hu'
  have hmi := Nat.add_mul_lt_mul_of_lt_of_lt hj hi
  have hnj := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
  have hnm := Nat.mul_comm n m
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hXY
  have hXo : ∀ c, xo.eval ≤ c → c < xo.eval + 2 * (m * n) →
      blockDisjoint (X, c, 1) (Y, yo.eval, 2 * (n * m)) = true := by
    intro c h1 h2
    simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
    omega
  have hX0 : st.store.read p X (xo.eval + 2 * (j + m * i)) = some (A ⟨j, hj⟩ ⟨i, hi⟩).1 := by
    simpa [pairLayout] using hA ⟨j, hj⟩ ⟨i, hi⟩ (0 : Fin 2)
  have hX1 : st.store.read p X (xo.eval + 2 * (j + m * i) + 1) = some (A ⟨j, hj⟩ ⟨i, hi⟩).2 := by
    simpa [pairLayout, Nat.add_assoc] using hA ⟨j, hj⟩ ⟨i, hi⟩ (1 : Fin 2)
  rw [hfr _ _ _ (hXo (xo.eval + 2 * (j + m * i)) (by omega) (by omega)), hX0,
    Option.some_inj] at ha
  rw [Store.read_of_write_eq_some_of_ne (b' := X) (i' := xo.eval + 2 * (j + m * i) + 1) hu
    (by omega), hfr _ _ _ (hXo (xo.eval + 2 * (j + m * i) + 1) (by omega) (by omega)), hX1,
    Option.some_inj] at hb
  subst ha hb
  refine ⟨fun i' j' hlt => ?_, fun q c d hd => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hl | he
    · obtain ⟨g1, g2⟩ := hD i' j' hl
      exact ⟨(Store.read_of_write_eq_some_of_ne hu' (Or.inr (by omega))).trans
          ((Store.read_of_write_eq_some_of_ne hu (Or.inr (by omega))).trans g1),
        (Store.read_of_write_eq_some_of_ne hu' (Or.inr (by omega))).trans
          ((Store.read_of_write_eq_some_of_ne hu (Or.inr (by omega))).trans g2)⟩
    · obtain ⟨e1, e2⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt i'.2 hi).1
        (show i'.1 + n * j'.1 = i + n * j by omega)
      obtain rfl : i' = ⟨i, hi⟩ := Fin.ext e1
      obtain rfl : j' = ⟨j, hj⟩ := Fin.ext e2
      refine ⟨(Store.read_of_write_eq_some_of_ne hu' (Or.inr (by omega))).trans
        ((Store.read_of_write_eq_some hu).trans ?_), (Store.read_of_write_eq_some hu').trans ?_⟩
      · rfl
      · simp [FloatMachine.conjTransposeMat, ScalarSem.toFloatMachine, hv]
  · have hd' := hd
    simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hd'
    rw [Store.read_of_write_eq_some_of_ne (b' := c) (i' := d) hu' (by omega),
      Store.read_of_write_eq_some_of_ne (b' := c) (i' := d) hu (by omega)]
    exact hfr q c d hd

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
  change exec I (.seq (.named _ _ (.seq (.loop (.const m) fun j => .seq (.loop (.const n) fun i =>
    .seq (.instr (.copy p ⟨Y, yo + zidx (.const n) (.var i) (.var j)⟩
      ⟨X, xo + zidx (.const m) (.var j) (.var i)⟩))
    (.seq (.instr (.un p .neg ⟨Y, yo + zidx (.const n) (.var i) (.var j) + 1⟩
      ⟨X, xo + zidx (.const m) (.var j) (.var i) + 1⟩)) .skip)) .skip) .skip)) .skip) st =
    some st' at h
  rw [exec_seq_skip, exec_named, exec_seq_skip] at h
  -- the outer loop over the columns $j$; the inner loop over the rows $i$
  obtain ⟨hG, hOUT⟩ := forall_of_exec_loop_eq_some I
    (fun j => ZConjInv p n m Y yo.eval st
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).conjTransposeMat A) (n * j))
    ⟨fun i j' hlt => absurd hlt (Nat.not_lt_zero _), fun q b c _ => rfl⟩
    (fun j hj s₁ s₂ hs hr => by
      rw [exec_seq_skip] at hr
      have hn : n * (j + 1) = n * j + n := by ring
      rw [hn]
      exact forall_of_exec_loop_eq_some I (n := .const n)
        (fun i => ZConjInv p n m Y yo.eval st
          ((I.sem.toFloatMachine p toNat mmR qrR unif normal).conjTransposeMat A) (n * j + i))
        hs (fun i hi t₁ t₂ ht hr' => ZConjInv.step hA hXY hi hj ht hr') hr) h
  refine ⟨fun i j ⟨t, ht⟩ => ?_, hOUT⟩
  have := Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2
  obtain ⟨g1, g2⟩ := hG i j (by simpa using this)
  change t < 2 at ht
  rcases t with _ | _ | t
  · simpa [pairLayout] using g1
  · simpa [pairLayout, Nat.add_assoc] using g2
  · omega

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
  change exec I (.seq (.named _ _ (.seq (.instr (.lit p dst 0)) (.seq (.loop _ fun i =>
    .seq (.instr (.bin p .add dst dst ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩)) .skip)
    .skip))) .skip) st = some st' at h
  rw [exec_seq_skip, exec_named] at h
  obtain ⟨v0, s0, hv0, hs0, h⟩ := exists_of_exec_seq_lit h
  rw [exec_seq_skip] at h
  have hne_of : ∀ b j, blockDisjoint (b, j, 1) (dst.buf, dst.idx.eval, 1) = true →
      b ≠ dst.buf ∨ j ≠ dst.idx.eval := by
    intro b j hd
    simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hd
    omega
  -- the diagonal real parts, outside the cell `dst`
  have hXd : ∀ i (hi : i < n),
      blockDisjoint (X, xo.eval + 2 * (i + n * i), 1) (dst.buf, dst.idx.eval, 1) = true ∧
        st.store.read p X (xo.eval + 2 * (i + n * i)) = some (A ⟨i, hi⟩ ⟨i, hi⟩).1 := by
    intro i hi
    have := Nat.add_mul_lt_mul_of_lt_of_lt hi hi
    refine ⟨?_, by simpa [pairLayout] using hA ⟨i, hi⟩ ⟨i, hi⟩ (0 : Fin 2)⟩
    simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hdX ⊢
    omega
  -- the loop keeps the fold of the first $k$ diagonal real parts in the cell `dst`
  refine (fun hR => ?_) (forall_of_exec_loop_eq_some I (fun k s =>
      s.store.read p dst.buf dst.idx.eval = some (((List.finRange n).take k).foldl
        (fun acc j => M.add acc (A j j).1) M.zero) ∧
      ∀ q b j, blockDisjoint (b, j, 1) (dst.buf, dst.idx.eval, 1) = true →
        s.store.read q b j = st.store.read q b j)
    ⟨(Store.read_of_write_eq_some hs0).trans (by simp [hM, ScalarSem.toFloatMachine, hv0]),
      fun q b j hd => Store.read_of_write_eq_some_of_ne hs0 (hne_of b j hd)⟩ ?_ h)
  · obtain ⟨hdst, hout⟩ := hR
    rw [List.take_of_length_le (by simp)] at hdst
    exact ⟨hdst, hout⟩
  intro k hk s₁ s₂ ⟨hd, hfr⟩ hr
  change k < n at hk
  obtain ⟨a, x, v, s, ha, hx, hv, hw, hr⟩ := exists_of_exec_seq_bin hr
  rw [exec_skip, Option.some_inj] at hr
  subst hr
  simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
    IExp.eval_ofNat] at hx
  rw [hd, Option.some_inj] at ha
  rw [hfr _ _ _ (hXd k hk).1, (hXd k hk).2, Option.some_inj] at hx
  subst ha hx
  refine ⟨?_, fun q b j hdj =>
    (Store.read_of_write_eq_some_of_ne hw (hne_of b j hdj)).trans (hfr q b j hdj)⟩
  have hfold : ((List.finRange n).take (k + 1)).foldl (fun acc j => M.add acc (A j j).1) M.zero =
      M.add (((List.finRange n).take k).foldl (fun acc j => M.add acc (A j j).1) M.zero)
        (A ⟨k, hk⟩ ⟨k, hk⟩).1 := by
    rw [List.take_add_one, List.foldl_append]
    simp [hk]
  rw [Store.read_of_write_eq_some hw, hfold]
  change some v = some ((I.sem.bin p .add _ _).getD default)
  rw [hv, Option.getD_some]

end NLAlib.Computation
