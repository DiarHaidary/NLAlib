/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.BottomLevel
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.UpLevel
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Transfer

/-!
# Every successful run of the spectral bisection program writes `eigh`

Under kernels that are routines on pairs, a semantics that decides flags, exact integer literals up
to $n + 4$ and the exact floor conversion, every successful run of `NLAlib.eighProg` writes exactly
`NLAlib.eigh` on the machine of the interpretation (`NLAlib.eighTapeMachine`) with the tree of
samples at the slots: the downward pass computes the nodes level by level, the spent level the junk
outputs, and the upward pass assembles the outputs.

## Main results

* `NLAlib.holds_of_exec_eighProg`: the refinement (partial equality) for the builder.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}


/-- **The downward pass**: from the initialisation (the root at depth $0$, every size cell
below it $0$, the constants and the stored $R_0$, $\beta$), the loop of
`NLAlib.eighDownLevel` over the depths $d \le \ell_0$ ends with the nodes of depth $\ell_0 + 1$ and,
for every lower depth, its nodes and records (the precise frame of
`levelHolds_succ_of_exec_eighDownLevel` keeps them); every cell outside the arenas and the sample
buffers is kept. -/
private theorem holds_of_exec_eighDownLoop {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F : ℕ) (hn1 : 1 ≤ n) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {σ0 σd : St P K C}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hH : ∀ s : Store P K, s.shape = σ0.store.shape → H.Shaped s p n (ℓ₀ + 1))
    (hpos : σ0.pos .uniform = 0 ∧ σ0.pos .gaussian = 0)
    (hlev : H.LevelHolds I.sem σ0.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ 0)
    (hz : ∀ e lo, 0 < e → e ≤ ℓ₀ + 1 → lo < n →
      ReadsIdx I.sem σ0.store p H.Sz (n * e + lo) 0)
    (hpar : σ0.store.read p par 0 = some R₀ ∧ σ0.store.read p par 2 = some β)
    (hc : σ0.store.read p c 0 = I.sem.lit p 1 ∧
      σ0.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      σ0.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      σ0.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      σ0.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (.loop (.const ℓ₀ + 1) fun d => (eighDownLevel p mm qr (.const n) (.const ℓ₀)
      (.const F) (.var d) par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩
      ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run) σ0 = some σd) :
    σd.store.shape = σ0.store.shape ∧
      H.LevelHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1) ∧
      (∀ e < ℓ₀ + 1, H.LevelHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
          ⟨n, A₀, R₀, ε, ℓ₀⟩ e ∧
        H.RecordHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F R₀ β
          ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      ∀ q b i, b ∉ H.handles → b ≠ Su → b ≠ Sg → σd.store.read q b i = σ0.store.read q b i := by
  set M := eighTapeMachine I p mmR qrR with hM
  have hnd : H.handles.Nodup := (List.nodup_append.mp hbufs).1
  have hdis := (List.nodup_append.mp hbufs).2.2
  have hparH : par ∉ H.handles := fun hm => hdis par hm par (by simp) rfl
  have hcH : c ∉ H.handles := fun hm => hdis c hm c (by simp) rfl
  have hSu : Su ∉ H.handles := fun hm => hdis Su hm Su (by simp) rfl
  have hSg : Sg ∉ H.handles := fun hm => hdis Sg hm Sg (by simp) rfl
  have h4 := (List.nodup_append.mp hbufs).2.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h4
  obtain ⟨⟨hparSu, hparSg, -⟩, ⟨-, hSuc⟩, hSgc, -⟩ := h4
  have hR := forall_of_exec_loop_eq_some I (st := σ0) (fun d (s : St P K C) =>
      s.store.shape = σ0.store.shape ∧ s.pos .uniform = n * d ∧
      s.pos .gaussian = 4 * (n * n) * d ∧
      H.LevelHolds I.sem s.store p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ d ∧
      (∀ e < d, H.LevelHolds I.sem s.store p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e ∧
        H.RecordHolds I.sem s.store p M n F R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ e lo, d < e → e ≤ ℓ₀ + 1 → lo < n → ReadsIdx I.sem s.store p H.Sz (n * e + lo) 0) ∧
      (∀ q b i, b ∉ H.handles → b ≠ Su → b ≠ Sg → s.store.read q b i = σ0.store.read q b i))
    ⟨rfl, by rw [hpos.1, Nat.mul_zero], by rw [hpos.2, Nat.mul_zero], hlev,
      fun e he => absurd he (Nat.not_lt_zero _), hz, fun _ _ _ _ _ _ => rfl⟩ ?_ h
  · obtain ⟨hsh, -, -, hL, hlow, -, hfr⟩ := hR
    exact ⟨hsh, hL, hlow, hfr⟩
  intro d hd s₁ s₂ ⟨hsh1, hpu1, hpg1, hL1, hlow1, hz1, hfr1⟩ hex
  change d < ℓ₀ + 1 at hd
  have hex' := (exec_eighDownLevel_var p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
    H.Kp c s₁).symm.trans hex
  have hcs : ∀ j, s₁.store.read p c j = σ0.store.read p c j := fun j =>
    hfr1 p c j hcH (Ne.symm hSuc) (Ne.symm hSgc)
  obtain ⟨hL2, hR2, hfr2, hsh2, hpu2, hpg2⟩ := levelHolds_succ_of_exec_eighDownLevel hmm hqr p hflag
      hcmp
    n ℓ₀ F d (ℓ₀ + 1) hd hlit htn H (par := par) (Su := Su) (Sg := Sg) (c := c)
    (hH _ hsh1) hbufs hL1 (fun lo hlo => hz1 (d + 1) lo (by omega) (by omega) hlo)
    ⟨hpu1, hpg1⟩
    ⟨(hfr1 p par 0 hparH hparSu hparSg).trans hpar.1,
      (hfr1 p par 2 hparH hparSu hparSg).trans hpar.2⟩
    ⟨(hcs 0).trans hc.1, (hcs 1).trans hc.2.1, (hcs 2).trans hc.2.2.1,
      (hcs 3).trans hc.2.2.2.1, (hcs 4).trans hc.2.2.2.2⟩ hex'
  refine ⟨hsh2.trans hsh1, by rw [hpu2, hpu1]; ring, by rw [hpg2, hpg1]; ring, hL2,
    fun e he => ?_, fun e lo he1 he2 hlo => ?_, fun q b i hb h1 h2 => ?_⟩
  · have hL : H.LevelHolds I.sem s₁.store p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
      · exact (hlow1 e he).1
      · exact hL1
    refine ⟨EighArenas.LevelHolds.of_read_eq_of_one_le hn1 (fun q b i hb hlc => hfr2 q b i
      (fun e => hSu (e ▸ mem_handles_of_node_arena hb)) (fun e => hSg (e ▸ mem_handles_of_node_arena
          hb))
      (fun h => false_of_node_arena_of_record_arena hnd hb h.1)
      (fun h => by have := eq_of_levelCell_of_levelCell hnd hlc h; omega)) hL, ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he' | rfl
    · exact EighArenas.RecordHolds.of_read_eq (fun q b i hb hlc => hfr2 q b i
        (fun e => hSu (e ▸ mem_handles_of_record_arena hb)) (fun e => hSg (e ▸
            mem_handles_of_record_arena hb))
        (fun h => by have := eq_of_levelCell_of_levelCell hnd hlc h.2; omega)
        (fun h => by have := eq_of_levelCell_of_levelCell hnd hlc h; omega)) (hlow1 e he').2
    · exact hR2
  · have hlc : H.LevelCell n e H.Sz (n * e + lo) :=
      Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by rw [Nat.mul_succ]; omega⟩)
    have hSzm : H.Sz = H.Ma ∨ H.Sz = H.Sz ∨ H.Sz = H.Lv := Or.inr (Or.inl rfl)
    exact readsIdx_of_read_eq (hfr2 p H.Sz (n * e + lo)
      (fun e => hSu (e ▸ mem_handles_of_node_arena hSzm)) (fun e => hSg (e ▸
          mem_handles_of_node_arena hSzm))
      (fun h => false_of_node_arena_of_record_arena hnd hSzm h.1)
      (fun h => by have := eq_of_levelCell_of_levelCell hnd hlc h; omega))
      (hz1 e lo (by omega) he2 hlo)
  · refine (hfr2 q b i h1 h2 (fun h => hb ?_) (fun h => hb (mem_handles_of_levelCell h))).trans
      (hfr1 q b i hb h1 h2)
    obtain ⟨h', -⟩ := h
    exact mem_handles_of_record_arena (by rcases h' with h | h | h | h | h <;> simp [h])

/-- **The spent level and the upward pass**: from the nodes of depth $\ell_0 + 1$ and the
nodes and records of every lower depth, `NLAlib.eighBottomLevel` and the loop of
`NLAlib.eighUpLevel` over the depths $\ell_0, \ldots, 0$ end with the outputs of depth $0$; every
cell outside the output and eigenvalue arenas is kept. -/
private theorem holds_of_exec_eighUpLoop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {dec : P → K → ℝ} (p : P) (n ℓ₀ F : ℕ) (hn1 : 1 ≤ n)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {c : ℕ} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {σd σb σu : St P K C}
    (hnd : H.handles.Nodup)
    (hH : ∀ s : Store P K, s.shape = σd.store.shape → H.Shaped s p n (ℓ₀ + 1))
    (htwo : c ∉ H.handles) (htwov : σd.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlevD : H.LevelHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1))
    (hlow : ∀ e < ℓ₀ + 1, H.LevelHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀
        β ⟨n, A₀, R₀, ε, ℓ₀⟩ e ∧
      H.RecordHolds I.sem σd.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e)
    (hbot : exec I (eighBottomLevel (ι := ι) p (.const n) (.const (ℓ₀ + 1)) H.Ua H.Ea H.Sz).run
      σd = some σb)
    (h : exec I (.loop (.const ℓ₀ + 1) fun j => (eighUpLevel p mm (.const n) (.const ℓ₀ - .var j)
      H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 1⟩).run) σb = some σu) :
    σu.store.shape = σd.store.shape ∧
      H.OutHolds σu.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ 0 ∧
      ∀ q b i, b ≠ H.Ua → b ≠ H.Ea → σu.store.read q b i = σd.store.read q b i := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hOD, hfrB, hshB, -⟩ := holds_of_exec_eighBottomLevel p n ℓ₀ F (ℓ₀ + 1) hlit htn H
    (A := A₀) (ε := ε) (hH _ rfl) hlevD hbot
  have hR := forall_of_exec_loop_eq_some I (st := σb) (fun j (s : St P K C) =>
      s.store.shape = σd.store.shape ∧
      H.OutHolds s.store p M n F (ℓ₀ + 1) R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1 - j) ∧
      (∀ e < ℓ₀ + 1 - j, H.LevelHolds I.sem s.store p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e ∧
        H.RecordHolds I.sem s.store p M n F R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ q b i, b ≠ H.Ua → b ≠ H.Ea → s.store.read q b i = σd.store.read q b i))
    ⟨hshB, hOD, fun e he => ⟨EighArenas.LevelHolds.of_read_eq_of_one_le hn1
        (fun q b i hb hlc => hfrB q b i (fun h => false_of_node_arena_of_out_arena hnd hb h.1))
            (hlow e he).1,
      EighArenas.RecordHolds.of_read_eq (fun q b i hb hlc => hfrB q b i
        (fun h => by have := eq_of_levelCell_of_levelCell hnd hlc h.2; omega)) (hlow e he).2⟩,
      fun q b i h1 h2 => hfrB q b i (fun h => h.1.elim h1 h2)⟩ ?_ h
  · obtain ⟨hsh, hO, -, hfr⟩ := hR
    change H.OutHolds σu.store p M n F (ℓ₀ + 1) R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1 - (ℓ₀ + 1)) at hO
    rw [Nat.sub_self] at hO
    exact ⟨hsh, hO, hfr⟩
  intro j hj s₁ s₂ ⟨hsh1, hO1, hlow1, hfr1⟩ hex
  change j < ℓ₀ + 1 at hj
  have hex' : exec I (eighUpLevel p mm (.const n) (.const (ℓ₀ - j)) H.Lv H.Ua H.Qa H.Ea H.Sz
      H.Kd H.Kp ⟨c, 1⟩).run s₁ = some s₂ := by
    rw [← exec_eighUpLevel_of_eval_eq p mm n (ℓ₀ - j) (.const ℓ₀ - .var j) rfl]
    exact hex
  have e1 : ℓ₀ - j + 1 = ℓ₀ + 1 - j := by omega
  have hOut : H.OutHolds s₁.store p M n F (ℓ₀ + 1) R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ - j + 1) := by
    rw [e1]; exact hO1
  obtain ⟨hO2, hfr2, hsh2, -⟩ := holds_of_exec_eighUpLevel hmm p n ℓ₀ F (ℓ₀ - j) (ℓ₀ + 1)
    (by omega) hlit htn H (two := ⟨c, 1⟩) (A := A₀) (hH _ hsh1) htwo
    ((hfr1 p c 1 (fun h => htwo (by rw [h]; simp [EighArenas.handles]))
      (fun h => htwo (by rw [h]; simp [EighArenas.handles]))).trans htwov)
    (hlow1 _ (by omega)).1 (hlow1 _ (by omega)).2 hOut hex'
  have e2 : ℓ₀ + 1 - (j + 1) = ℓ₀ - j := by omega
  refine ⟨hsh2.trans hsh1, by rw [e2]; exact hO2, fun e he => ?_,
    fun q b i h1 h2 => (hfr2 q b i (fun h => h.1.elim h1 h2)).trans
      (hfr1 q b i h1 h2)⟩
  rw [e2] at he
  exact ⟨EighArenas.LevelHolds.of_read_eq_of_one_le hn1 (fun q b i hb hlc => hfr2 q b i
      (fun h => false_of_node_arena_of_out_arena hnd hb h.1)) (hlow1 e (by omega)).1,
    EighArenas.RecordHolds.of_read_eq (fun q b i hb hlc => hfr2 q b i
      (fun h => by have := eq_of_levelCell_of_levelCell hnd hlc h.2; omega)) (hlow1 e (by omega)).2⟩


omit [Inhabited K] in
/-- A run from an updated state is a run from a state with that store and the old tape positions. -/
private theorem exists_eq_of_exec_with {t : Stmt P ι ℕ ℕ} {S s' : St P K C} {W : Store P K}
    {c : C} (h : exec I t { S with store := W, cnt := c } = some s') :
    ∃ T : St P K C, T.store = W ∧ T.pos = S.pos ∧ exec I t T = some s' :=
  ⟨{ S with store := W, cnt := c }, rfl, rfl, h⟩

/-- **The constants of `NLAlib.eighProg`**: a successful run of the five instructions that write
one, $\mathrm{fl}(2)$, $\mathrm{fl}(1/2)$, $-1$ and $\sqrt{1/2}$ into the cells $0$ to $4$ of `t`,
then of `rest`, goes through a state whose cells $0$ to $4$ of `t` hold the constants of the
machine `NLAlib.eighTapeMachine I p mmR qrR`, with every other buffer, the shape and the positions
as at the start, and runs `rest` from there. -/
private theorem exec_eighConsts {p : P} {t : ℕ} {rest : Builder P ι ℕ ℕ Unit} {S s' : St P K C}
    (h : exec I (do
        ins (.lit p ⟨t, 0⟩ 1)
        ins (.litIdx p ⟨t, 1⟩ 2)
        ins (.bin p .div ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        ins (.un p .neg ⟨t, 3⟩ ⟨t, 0⟩)
        ins (.un p .sqrt ⟨t, 4⟩ ⟨t, 2⟩)
        rest : Builder P ι ℕ ℕ Unit).run S = some s') :
    ∃ T : St P K C, T.store.shape = S.store.shape ∧ T.pos = S.pos ∧
      (∀ q b i, b ≠ t → T.store.read q b i = S.store.read q b i) ∧
      T.store.read p t 0 = I.sem.lit p 1 ∧ T.store.read p t 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      T.store.read p t 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      T.store.read p t 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      T.store.read p t 4 = some (I.sem.sqrtHalf p) ∧ exec I rest.run T = some s' := by
  obtain ⟨v0, W1, hv0, hw1, g⟩ := exists_of_exec_seq_lit h
  obtain ⟨T1, hT1, hq1, g⟩ := exists_eq_of_exec_with g
  obtain ⟨v1, W2, hv1, hw2, g⟩ := exists_of_exec_seq_litIdx g
  obtain ⟨T2, hT2, hq2, g⟩ := exists_eq_of_exec_with g
  obtain ⟨a2, b2, v2, W3, ha2, hb2, hv2, hw3, g⟩ := exists_of_exec_seq_bin g
  obtain ⟨T3, hT3, hq3, g⟩ := exists_eq_of_exec_with g
  obtain ⟨a3, v3, W4, ha3, hv3, hw4, g⟩ := exists_of_exec_seq_un g
  obtain ⟨T4, hT4, hq4, g⟩ := exists_eq_of_exec_with g
  obtain ⟨a4, v4, W5, ha4, hv4, hw5, g⟩ := exists_of_exec_seq_un g
  obtain ⟨T5, hT5, hq5, g⟩ := exists_eq_of_exec_with g
  replace hw1 : S.store.write p t 0 v0 = some T1.store := by rw [hT1]; exact hw1
  replace hw2 : T1.store.write p t 1 v1 = some T2.store := by rw [hT2]; exact hw2
  replace hw3 : T2.store.write p t 2 v2 = some T3.store := by rw [hT3]; exact hw3
  replace hw4 : T3.store.write p t 3 v3 = some T4.store := by rw [hT4]; exact hw4
  replace hw5 : T4.store.write p t 4 v4 = some T5.store := by rw [hT5]; exact hw5
  replace hv1 : I.sem.lit p ((2 : ℕ) : ℚ) = some v1 := hv1
  have rd : ∀ {s s' : Store P K} {j : ℕ} {v : K} (k : ℕ), s.write p t j v = some s' →
      s'.read p t k = if k = j then some v else s.read p t k := by
    intro s s' j v k hw
    split_ifs with hk
    · subst hk; exact Store.read_of_write_eq_some hw
    · exact Store.read_of_write_eq_some_of_ne hw (Or.inr hk)
  replace ha2 : T2.store.read p t 0 = some a2 := ha2
  replace hb2 : T2.store.read p t 1 = some b2 := hb2
  replace ha3 : T3.store.read p t 0 = some a3 := ha3
  replace ha4 : T4.store.read p t 2 = some a4 := ha4
  replace ha2 : a2 = v0 := Option.some_inj.mp <| ha2.symm.trans (by simp [rd _ hw2, rd _ hw1])
  replace hb2 : b2 = v1 := Option.some_inj.mp <| hb2.symm.trans (by simp [rd _ hw2])
  replace ha3 : a3 = v0 := Option.some_inj.mp <| ha3.symm.trans
    (by simp [rd _ hw3, rd _ hw2, rd _ hw1])
  replace ha4 : a4 = v2 := Option.some_inj.mp <| ha4.symm.trans (by simp [rd _ hw4, rd _ hw3])
  rw [ha2, hb2] at hv2
  rw [ha3] at hv3
  rw [ha4] at hv4
  have r5 : ∀ k, T5.store.read p t k = if k = 4 then some v4 else if k = 3 then some v3 else
      if k = 2 then some v2 else if k = 1 then some v1 else if k = 0 then some v0 else
      S.store.read p t k := fun k => by
    simp only [rd _ hw5, rd _ hw4, rd _ hw3, rd _ hw2, rd _ hw1]
  refine ⟨T5, ?_, by rw [hq5, hq4, hq3, hq2, hq1], fun q b i hb => ?_, by simp [r5, hv0],
    by rw [r5, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl, hv1],
    ?_, ?_, ?_, g⟩
  · rw [Store.shape_of_write_eq_some hw5, Store.shape_of_write_eq_some hw4,
      Store.shape_of_write_eq_some hw3, Store.shape_of_write_eq_some hw2,
      Store.shape_of_write_eq_some hw1]
  · rw [Store.read_of_write_eq_some_of_ne hw5 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw4 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw3 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw2 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw1 (Or.inl hb)]
  · rw [r5]
    change some v2 = some ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
      ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)
    rw [hv0, hv1, Option.getD_some, Option.getD_some, hv2, Option.getD_some]
  · rw [r5]
    change some v3 = some ((I.sem.un p .neg ((I.sem.lit p 1).getD default)).getD default)
    rw [hv0, Option.getD_some, hv3, Option.getD_some]
  · rw [r5]
    unfold ScalarSem.sqrtHalf
    rw [hv0, hv1, Option.getD_some, Option.getD_some, hv2, Option.getD_some, hv4,
      Option.getD_some]
    rfl

/-- **The arenas of `NLAlib.eighProg` at their start**: for buffers `A`, `par` below `t`, a
successful run of the zero fill of the size arena `t + 5`, the size $n$ of the root in its cell
$0$, the copy of the block at offset $0$ of `A` (holding $\mathbf{A}$) into the node arena `t + 1`
and the copies of the cells $0$, $1$ of `par` (holding $R_0$, $\varepsilon$) into the window arena
`t + 8`, then of `rest`, goes through a state holding these, with every other buffer, the shape
and the positions as at the start, and runs `rest` from there. -/
private theorem exec_eighArenasInit {p : P} {n ℓ₀ t A par : ℕ}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε : K} {rest : Builder P ι ℕ ℕ Unit}
    {S s' : St P K C} (hAt : A < t) (hpart : par < t) (hA : pairLayout.Holds S.store p A 0 A₀)
    (hR₀ : S.store.read p par 0 = some R₀) (hε : S.store.read p par 1 = some ε)
    (h : exec I (do
        forRange (.const n * (.const ℓ₀ + 1 + 1) + 1) fun w => ins (.litIdx p ⟨t + 5, .var w⟩ 0)
        ins (.litIdx p ⟨t + 5, 0⟩ (.const n))
        zcopy p (.const n) (.const n) A 0 (t + 1) 0
        ins (.copy p ⟨t + 8, 0⟩ ⟨par, 0⟩)
        ins (.copy p ⟨t + 8, 1⟩ ⟨par, 1⟩)
        rest : Builder P ι ℕ ℕ Unit).run S = some s') :
    ∃ T : St P K C, T.store.shape = S.store.shape ∧ T.pos = S.pos ∧
      (∀ q b i, b ≠ t + 1 → b ≠ t + 5 → b ≠ t + 8 → T.store.read q b i = S.store.read q b i) ∧
      T.store.read p (t + 5) 0 = I.sem.lit p ((n : ℕ) : ℚ) ∧
      (∀ w, w ≠ 0 → w < n * (ℓ₀ + 1 + 1) + 1 →
        T.store.read p (t + 5) w = I.sem.lit p ((0 : ℕ) : ℚ)) ∧
      pairLayout.Holds T.store p (t + 1) 0 A₀ ∧ T.store.read p (t + 8) 0 = some R₀ ∧
      T.store.read p (t + 8) 1 = some ε ∧ exec I rest.run T = some s' := by
  obtain ⟨σ6, h6, g⟩ := exists_exec_and_exec_of_exec_seq h
  obtain ⟨v7, W7, hv7, hw7, g⟩ := exists_of_exec_seq_litIdx g
  obtain ⟨T7, hT7, hq7, g⟩ := exists_eq_of_exec_with g
  obtain ⟨σ8, h8, g⟩ := exists_exec_and_exec_of_exec_seq g
  obtain ⟨v9, W9, hv9, hw9, g⟩ := exists_of_exec_seq_copy g
  obtain ⟨T9, hT9, hq9, g⟩ := exists_eq_of_exec_with g
  obtain ⟨v10, W10, hv10, hw10, g⟩ := exists_of_exec_seq_copy g
  obtain ⟨T10, hT10, hq10, g⟩ := exists_eq_of_exec_with g
  replace hw7 : σ6.store.write p (t + 5) 0 v7 = some T7.store := by rw [hT7]; exact hw7
  replace hw9 : σ8.store.write p (t + 8) 0 v9 = some T9.store := by rw [hT9]; exact hw9
  replace hw10 : T9.store.write p (t + 8) 1 v10 = some T10.store := by rw [hT10]; exact hw10
  replace hv9 : σ8.store.read p par 0 = some v9 := hv9
  replace hv10 : T9.store.read p par 1 = some v10 := hv10
  obtain ⟨sh6, ps6, rd6, fr6⟩ := shape_of_exec_loop_litIdx h6
  have r7 : ∀ q b i, b ≠ t + 5 → T7.store.read q b i = S.store.read q b i := fun q b i hb => by
    rw [Store.read_of_write_eq_some_of_ne hw7 (Or.inl hb), fr6 q b i (Or.inl hb)]
  obtain ⟨hM8, fr8, sh8, ps8⟩ := holds_of_exec_zcopy (st := T7) p n n (X := A) (Y := t + 1)
    (xo := 0) (yo := 0) (pairLayout_holds_of_read_eq hA fun i _ _ => r7 p A i (by omega))
    (blockDisjoint_of_ne_compress (by omega)) ((exec_seq_skip I _ _).trans h8)
  have r8 : ∀ q b i, b ≠ t + 1 → b ≠ t + 5 → σ8.store.read q b i = S.store.read q b i :=
    fun q b i h1 h5 => (fr8 q b i (blockDisjoint_of_ne_compress h1)).trans (r7 q b i h5)
  have r10 : ∀ q b i, b ≠ t + 8 → T10.store.read q b i = σ8.store.read q b i := fun q b i hb => by
    rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw9 (Or.inl hb)]
  have e9 : v9 = R₀ := Option.some_inj.mp <|
    hv9.symm.trans ((r8 p par 0 (by omega) (by omega)).trans hR₀)
  have e10 : v10 = ε := Option.some_inj.mp <| hv10.symm.trans
    ((Store.read_of_write_eq_some_of_ne hw9 (Or.inl (by omega))).trans
      ((r8 p par 1 (by omega) (by omega)).trans hε))
  refine ⟨T10, ?_, by rw [hq10, hq9, ps8, hq7, ps6],
    fun q b i h1 h5 h8 => (r10 q b i h8).trans (r8 q b i h1 h5), ?_, fun w hw0 hw => ?_,
    pairLayout_holds_of_read_eq hM8 fun i _ _ => r10 p _ i (by omega), ?_, ?_, g⟩
  · rw [Store.shape_of_write_eq_some hw10, Store.shape_of_write_eq_some hw9, sh8,
      Store.shape_of_write_eq_some hw7, sh6]
  · rw [r10 p _ 0 (by omega), fr8 p _ 0 (blockDisjoint_of_ne_compress (by omega)),
      Store.read_of_write_eq_some hw7]
    exact hv7.symm
  · rw [r10 p _ w (by omega), fr8 p _ w (blockDisjoint_of_ne_compress (by omega)),
      Store.read_of_write_eq_some_of_ne hw7 (Or.inr hw0)]
    exact rd6 w hw
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inr (by decide)),
      Store.read_of_write_eq_some hw9, e9]
  · rw [Store.read_of_write_eq_some hw10, e10]

omit [AddMonoid C] [Inhabited K] in
/-- **The root at depth $0$**: a store whose size arena holds $n \ge 1$ in its cell $0$ and $0$ in
its cells $1, \ldots, n(\ell_0 + 2)$, whose node arena holds $\mathbf{A}$ at offset $0$ and whose
window arena holds $R_0$, $\varepsilon$ in its cells $0$, $1$ holds the nodes of depth $0$, under
exact integer literals up to $n + 4$ and the exact floor conversion. -/
private theorem levelHolds_zero_of_init {dec : P → K → ℝ} {p : P} {M : FloatMachine K ℕ ℕ}
    {n ℓ₀ F : ℕ} (hn : 0 < n) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) {H : EighArenas} {W : Store P K}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hSz0 : W.read p H.Sz 0 = I.sem.lit p ((n : ℕ) : ℚ))
    (hSz : ∀ w, w ≠ 0 → w < n * (ℓ₀ + 1 + 1) + 1 → W.read p H.Sz w = I.sem.lit p ((0 : ℕ) : ℚ))
    (hMa : pairLayout.Holds W p H.Ma 0 A₀) (hLv0 : W.read p H.Lv 0 = some R₀)
    (hLv1 : W.read p H.Lv 1 = some ε) :
    H.LevelHolds I.sem W p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ 0 := by
  refine ⟨fun a lo y ha hl => ?_, fun lo hlo hno => ?_, hLv0, hLv1⟩
  · obtain rfl := List.eq_nil_of_length_eq_zero ha
    simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨readsIdx_of_read_eq_lit hlit htn (k := n) (by omega) (by rw [Nat.mul_zero]; exact hSz0),
      by rw [Nat.mul_zero, Nat.mul_zero]; exact hMa⟩
  · have hlo0 : lo ≠ 0 := by
      rintro rfl
      exact hno [] ⟨n, A₀, R₀, ε, ℓ₀⟩ rfl rfl
    have : n ≤ n * (ℓ₀ + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
    exact readsIdx_of_read_eq_lit hlit htn (k := 0) (by omega)
      (by rw [Nat.mul_zero, Nat.zero_add]; exact hSz lo hlo0 (by omega))

/-- **The passes and the copies out**: from a state whose arenas `H` hold the root at depth $0$,
with every size cell below it $0$, the tape positions at $0$, $R_0$, $\beta$ in the cells $0$, $2$
of `par` and the constants in `c`, a successful run of the downward pass, the spent level, the
upward pass and the copies of the root's output into the buffers `U`, `dv` outside the arenas ends
with that output, `NLAlib.eigh` with the tree of samples at the slots, in `U` and `dv`, and the
store shape kept. -/
private theorem holds_of_exec_eighPasses {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F : ℕ) (hn1 : 1 ≤ n) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c U dv : ℕ}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {T s' : St P K C}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (hU : U ∉ H.handles) (hdv : dv ∉ H.handles)
    (hUdv : U ≠ dv) (hH : ∀ s : Store P K, s.shape = T.store.shape → H.Shaped s p n (ℓ₀ + 1))
    (hpos : T.pos .uniform = 0 ∧ T.pos .gaussian = 0)
    (hlev : H.LevelHolds I.sem T.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ 0)
    (hz : ∀ e lo, 0 < e → e ≤ ℓ₀ + 1 → lo < n → ReadsIdx I.sem T.store p H.Sz (n * e + lo) 0)
    (hpar : T.store.read p par 0 = some R₀ ∧ T.store.read p par 2 = some β)
    (hc : T.store.read p c 0 = I.sem.lit p 1 ∧ T.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      T.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      T.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      T.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (do
        forRange (.const ℓ₀ + 1) fun d =>
          eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par H.Lv Su Sg H.Ma
            H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
        eighBottomLevel p (.const n) (.const ℓ₀ + 1) H.Ua H.Ea H.Sz
        forRange (.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
            ⟨c, 1⟩
        zcopy p (.const n) (.const n) H.Ua 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨H.Ea, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run T = some s') :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M n F R₀ β 0 0 ⟨n, A₀, R₀, ε, ℓ₀⟩)
    s'.store.shape = T.store.shape ∧ pairLayout.Holds s'.store p U 0 r.1 ∧
      ∀ i : Fin n, s'.store.read p dv i = some (r.2 i) := by
  intro M r
  obtain ⟨σd, hdown, g⟩ := exists_exec_and_exec_of_exec_seq h
  obtain ⟨σb, hbot, g⟩ := exists_exec_and_exec_of_exec_seq g
  obtain ⟨σu, hup, g⟩ := exists_exec_and_exec_of_exec_seq g
  obtain ⟨σz, hzc, g⟩ := exists_exec_and_exec_of_exec_seq g
  change exec I (.seq (.loop _ _) .skip) σz = some s' at g
  rw [exec_seq_skip] at g
  obtain ⟨hshD, hLD, hlowD, hfrD⟩ := holds_of_exec_eighDownLoop hmm hqr p hflag hcmp n ℓ₀ F hn1
    hlit htn H (A₀ := A₀) (ε := ε) hbufs hH hpos hlev hz hpar hc hdown
  have hbot' : exec I (eighBottomLevel (ι := ι) p (.const n) (.const (ℓ₀ + 1)) H.Ua H.Ea
      H.Sz).run σd = some σb := by
    rw [← exec_eighBottomLevel_of_eval_eq p n (ℓ₀ + 1) (IExp.const ℓ₀ + 1) rfl]
    exact (exec_seq_skip I _ _).trans hbot
  have hnd : H.handles.Nodup := (List.nodup_append.mp hbufs).1
  have hcH : c ∉ H.handles := fun hm => List.disjoint_of_nodup_append hbufs hm (by simp)
  have h4 := (List.nodup_append.mp hbufs).2.1
  have hcD : σd.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) := by
    rw [hfrD p c 1 hcH (fun h => by simp [h] at h4) (fun h => by simp [h] at h4)]
    exact hc.2.1
  obtain ⟨hshU, hO0, -⟩ := holds_of_exec_eighUpLoop hmm p n ℓ₀ F hn1 hlit htn H (c := c)
    (A₀ := A₀) (ε := ε) hnd (fun s hs => hH s (hs.trans hshD)) hcH hcD hLD hlowD hbot' hup
  obtain ⟨hU0, hE0⟩ := hO0 [] 0 ⟨n, A₀, R₀, ε, ℓ₀⟩ rfl rfl
  have hU0' : pairLayout.Holds σu.store p H.Ua (0 : IExp ℕ).eval r.1 := by
    have e : 2 * (n * n) * 0 + 2 * n * 0 = 0 := by ring
    rw [e] at hU0
    exact hU0
  have hUa : U ≠ H.Ua := fun h => hU (h ▸ by simp [EighArenas.handles])
  have hEa : H.Ea ≠ U := fun h => hU (h ▸ by simp [EighArenas.handles])
  obtain ⟨hUz, frz, shz, -⟩ := holds_of_exec_zcopy (st := σu) p n n (X := H.Ua) (Y := U)
    (xo := 0) (yo := 0) hU0' (blockDisjoint_of_ne_compress hUa) ((exec_seq_skip I _ _).trans hzc)
  obtain ⟨shc, hcp, frc⟩ := shape_of_exec_loop_copy (X := H.Ea) (Y := dv)
    (fun h => hdv (h ▸ by simp [EighArenas.handles])) g
  refine ⟨shc.trans (shz.trans (hshU.trans hshD)),
    pairLayout_holds_of_read_eq hUz fun i _ _ => frc p U i (Or.inl hUdv), fun i => ?_⟩
  rw [hcp i i.isLt, frz p H.Ea i (blockDisjoint_of_ne_compress hEa)]
  have := hE0 i
  simp only [Nat.mul_zero, Nat.zero_add] at this
  exact this

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The handles of the arenas, the parameters, the samples and the constants of `NLAlib.eighProg`
are distinct. -/
private theorem nodup_eighProg_handles {t par : ℕ} (hp : par < t) :
    ([t + 1, t + 2, t + 3, t + 4, t + 5, t + 6, t + 7, t + 8] ++
      [par, t + 9, t + 10, t]).Nodup := by
  simp
  omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A handle $b \le t$ is not one of the arenas `t + 1`, …, `t + 8` of `NLAlib.eighProg`. -/
private theorem not_mem_eighProg_arenas {t b : ℕ} (hb : b ≤ t) :
    b ∉ [t + 1, t + 2, t + 3, t + 4, t + 5, t + 6, t + 7, t + 8] := by
  simp
  omega

/-- **The body of `NLAlib.eighProg`** after its eleven allocations (the constants at `t`, the
arenas at `t + 1` to `t + 8`, the samples at `t + 9`, `t + 10`), for the buffers `A`, `par`, `U`,
`dv` below `t` with `U ≠ dv`: from a state that reads as `st` below `t` and whose arenas have the
shapes of the allocations, a successful run ends with the root's output of `NLAlib.eigh` in `U` and
`dv`, with the store shape kept. -/
private theorem holds_of_exec_eighProgBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F : ℕ) (hn1 : n > 0) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) {A par U dv t : ℕ} {st S s11 : St P K C}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} (hAt : A < t) (hpart : par < t)
    (hUt : U < t) (hdvt : dv < t) (hUdv : U ≠ dv) (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0)
    (hold : ∀ q b i, b < t → S.store.read q b i = st.store.read q b i) (hposS : S.pos = st.pos)
    (hsh1 : S.store.shape[t + 1]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)))
    (hsh2 : S.store.shape[t + 2]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)))
    (hsh3 : S.store.shape[t + 3]? = some (p, 2 * (n * n) * (ℓ₀ + 1)))
    (hsh4 : S.store.shape[t + 4]? = some (p, n * (ℓ₀ + 1 + 1)))
    (hsh5 : S.store.shape[t + 5]? = some (p, n * (ℓ₀ + 1 + 1) + 1))
    (hsh6 : S.store.shape[t + 6]? = some (p, n * (ℓ₀ + 1)))
    (hsh7 : S.store.shape[t + 7]? = some (p, n * (ℓ₀ + 1)))
    (hsh8 : S.store.shape[t + 8]? = some (p, 2 * (ℓ₀ + 1 + 1)))
    (h : exec I (do
        ins (.lit p ⟨t, 0⟩ 1)
        ins (.litIdx p ⟨t, 1⟩ 2)
        ins (.bin p .div ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        ins (.un p .neg ⟨t, 3⟩ ⟨t, 0⟩)
        ins (.un p .sqrt ⟨t, 4⟩ ⟨t, 2⟩)
        forRange (.const n * (.const ℓ₀ + 1 + 1) + 1) fun w => ins (.litIdx p ⟨t + 5, .var w⟩ 0)
        ins (.litIdx p ⟨t + 5, 0⟩ (.const n))
        zcopy p (.const n) (.const n) A 0 (t + 1) 0
        ins (.copy p ⟨t + 8, 0⟩ ⟨par, 0⟩)
        ins (.copy p ⟨t + 8, 1⟩ ⟨par, 1⟩)
        forRange (.const ℓ₀ + 1) fun d =>
          eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par (t + 8) (t + 9)
            (t + 10) (t + 1) (t + 2) (t + 3) (t + 4) (t + 5) (t + 6) (t + 7) ⟨t, 0⟩ ⟨t, 1⟩ ⟨t, 2⟩
            ⟨t, 3⟩ ⟨t, 4⟩
        eighBottomLevel p (.const n) (.const ℓ₀ + 1) (t + 2) (t + 4) (t + 5)
        forRange (.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') (t + 8) (t + 2) (t + 3) (t + 4)
            (t + 5) (t + 6) (t + 7) ⟨t, 1⟩
        zcopy p (.const n) (.const n) (t + 2) 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨t + 4, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run S = some s11) :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M n F R₀ β 0 0 ⟨n, A₀, R₀, ε, ℓ₀⟩)
    s11.store.shape = S.store.shape ∧ pairLayout.Holds s11.store p U 0 r.1 ∧
      ∀ i : Fin n, s11.store.read p dv i = some (r.2 i) := by
  obtain ⟨T5, sh5, ps5, fr5, c0, c1, c2, c3, c4, g⟩ := exec_eighConsts (mmR := mmR) (qrR := qrR) h
  have hold5 : ∀ q b i, b < t → T5.store.read q b i = st.store.read q b i := fun q b i hb =>
    (fr5 q b i (by omega)).trans (hold q b i hb)
  obtain ⟨T, shT, psT, frT, hSz0, hSz, hMa, hLv0, hLv1, g⟩ := exec_eighArenasInit hAt hpart
    (pairLayout_holds_of_read_eq hA fun i _ _ => hold5 p A i hAt) ((hold5 p par 0 hpart).trans
        hpar.1)
    ((hold5 p par 1 hpart).trans hpar.2.1) g
  have hcT : ∀ j, T.store.read p t j = T5.store.read p t j := fun j =>
    frT p t j (by omega) (by omega) (by omega)
  let H : EighArenas := ⟨t + 1, t + 2, t + 3, t + 4, t + 5, t + 6, t + 7, t + 8⟩
  have hbufs : (H.handles ++ [par, t + 9, t + 10, t]).Nodup := nodup_eighProg_handles hpart
  have hshT : T.store.shape = S.store.shape := shT.trans sh5
  have HS : ∀ s : Store P K, s.shape = T.store.shape → H.Shaped s p n (ℓ₀ + 1) := by
    intro s hs
    unfold EighArenas.Shaped
    rw [hs, hshT]
    exact ⟨(List.nodup_append.mp hbufs).1, hsh1, hsh2, hsh3, hsh4, hsh5, hsh6, hsh7, hsh8⟩
  have hparT : ∀ j, T.store.read p par j = st.store.read p par j := fun j =>
    (frT p par j (by omega) (by omega) (by omega)).trans (hold5 p par j hpart)
  have := holds_of_exec_eighPasses hmm hqr p hflag hcmp n ℓ₀ F hn1 hlit htn H hbufs
    (not_mem_eighProg_arenas hUt.le) (not_mem_eighProg_arenas hdvt.le) hUdv HS
    (by rw [psT, ps5, hposS]; exact hpos) (levelHolds_zero_of_init hn1 hlit htn hSz0 hSz hMa hLv0
      hLv1)
    (fun e lo he1 he2 hlo => by
      have h1 : n * e ≤ n * (ℓ₀ + 1) := Nat.mul_le_mul_left _ he2
      have h2 : n ≤ n * e := Nat.le_mul_of_pos_right _ he1
      have h3 : n * (ℓ₀ + 1 + 1) = n * (ℓ₀ + 1) + n := by ring
      exact readsIdx_of_read_eq_lit hlit htn (k := 0) (by omega) (hSz _ (by omega) (by omega)))
    ⟨(hparT 0).trans hpar.1, (hparT 2).trans hpar.2.2⟩
    ⟨(hcT 0).trans c0, (hcT 1).trans c1, (hcT 2).trans c2, (hcT 3).trans c3, (hcT 4).trans c4⟩ g
  exact ⟨this.1.trans hshT, this.2⟩

/-- Two stores agree below `m`: the same shape entries and the same reads at every buffer
`b < m`. -/
private def StoreAgree (m : ℕ) (s s' : Store P K) : Prop :=
  ∀ b < m, s.shape[b]? = s'.shape[b]? ∧ ∀ q i, s.read q b i = s'.read q b i

omit [Inhabited K] in
/-- A pushed store agrees with the store under it below its size. -/
private theorem storeAgree_push {s s' : Store P K} {x : P × Array (Option K)} {m : ℕ}
    (h : s' = s.push x) (hm : m ≤ s.size) : StoreAgree m s' s := fun b hb => by
  subst h
  exact ⟨Store.getElem?_shape_push_of_lt _ (by omega), fun q i => Store.read_push_of_lt (by omega)⟩

omit [Inhabited K] in
/-- Agreement below `m'` and then below `m ≤ m'` composes to agreement below `m`. -/
private theorem StoreAgree.trans {m m' : ℕ} {s₁ s₂ s₃ : Store P K} (h₁ : StoreAgree m' s₁ s₂)
    (h₂ : StoreAgree m s₂ s₃) (hm : m ≤ m') : StoreAgree m s₁ s₃ := fun b hb =>
  ⟨(h₁ b (by omega)).1.trans (h₂ b hb).1,
    fun q i => ((h₁ b (by omega)).2 q i).trans ((h₂ b hb).2 q i)⟩

omit [Inhabited K] in
/-- Eleven pops of a store of $t + 11$ buffers read as it below `t`. -/
private theorem read_of_eq_pop_eleven {s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ : Store P K} {t : ℕ}
    (h₁ : s₀ = s₁.pop) (h₂ : s₁ = s₂.pop) (h₃ : s₂ = s₃.pop) (h₄ : s₃ = s₄.pop)
    (h₅ : s₄ = s₅.pop) (h₆ : s₅ = s₆.pop) (h₇ : s₆ = s₇.pop) (h₈ : s₇ = s₈.pop)
    (h₉ : s₈ = s₉.pop) (h₁₀ : s₉ = s₁₀.pop) (h₁₁ : s₁₀ = s₁₁.pop) (hs : s₁₁.size = t + 11) :
    ∀ q b i, b < t → s₀.read q b i = s₁₁.read q b i := by
  subst h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁
  intro q b i hb
  repeat rw [Store.read_pop_of_lt (by simp only [Array.size_pop, hs]; omega)]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The tree of `NLAlib.eighProg`, its eleven allocations and its body. -/
private theorem eighProg_run_eq (p : P) (mm qr : ι) (n ℓ₀ F A par U dv : ℕ) :
    (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run =
      .seq (.alloc p 5 fun c => .alloc p (2 * (.const n * .const n) * (.const ℓ₀ + 1 + 1)) fun Ma =>
        .alloc p (2 * (.const n * .const n) * (.const ℓ₀ + 1 + 1)) fun Ua =>
        .alloc p (2 * (.const n * .const n) * (.const ℓ₀ + 1)) fun Qa =>
        .alloc p (.const n * (.const ℓ₀ + 1 + 1)) fun Ea =>
        .alloc p (.const n * (.const ℓ₀ + 1 + 1) + 1) fun Sz =>
        .alloc p (.const n * (.const ℓ₀ + 1)) fun Kd =>
        .alloc p (.const n * (.const ℓ₀ + 1)) fun Kp =>
        .alloc p (2 * (.const ℓ₀ + 1 + 1)) fun Lv =>
        .alloc p (.const n) fun Su =>
        .alloc p (4 * (.const n * .const n)) fun Sg => (do
        ins (.lit p ⟨c, 0⟩ 1)
        ins (.litIdx p ⟨c, 1⟩ 2)
        ins (.bin p .div ⟨c, 2⟩ ⟨c, 0⟩ ⟨c, 1⟩)
        ins (.un p .neg ⟨c, 3⟩ ⟨c, 0⟩)
        ins (.un p .sqrt ⟨c, 4⟩ ⟨c, 2⟩)
        forRange (.const n * (.const ℓ₀ + 1 + 1) + 1) fun w => ins (.litIdx p ⟨Sz, .var w⟩ 0)
        ins (.litIdx p ⟨Sz, 0⟩ (.const n))
        zcopy p (.const n) (.const n) A 0 Ma 0
        ins (.copy p ⟨Lv, 0⟩ ⟨par, 0⟩)
        ins (.copy p ⟨Lv, 1⟩ ⟨par, 1⟩)
        forRange (.const ℓ₀ + 1) fun d =>
          eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv Su Sg Ma Ua Qa
            Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
        eighBottomLevel p (.const n) (.const ℓ₀ + 1) Ua Ea Sz
        forRange (.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩
        zcopy p (.const n) (.const n) Ua 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨Ea, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run) .skip := by
  rfl


/-- **The refinement of the spectral bisection program, partial equality**: let the kernels `mm`,
`qr` of `I` be the routines `mmR`, `qrR` on interleaved pairs, and the semantics decide flags at
`p`, with exact integer literals up to $n + 4$ and the exact floor conversion. A successful run of
`NLAlib.eighProg` at size $n$, depth counter $\ell_0$ and step limit $F$, from a state with the tape
positions at $0$, whose block at offset $0$ of `A` holds the stored $\mathbf{A}$ and whose cells
$0$, $1$, $2$ of `par` hold $R_0$, $\varepsilon$, $\beta$, ends with the block at offset $0$ of `U`
and the cells $0, \ldots, n - 1$ of `dv` holding exactly
$$\mathsf{eigh}(\mathbf{A}, R_0, \varepsilon, \beta)$$
computed by `NLAlib.eigh` with step limit $F$ and depth counter $\ell_0$ on the machine of the
interpretation (`NLAlib.eighTapeMachine`), with the tree of samples at the slots
(`NLAlib.eighSlotTree`). [Shah2024, Algorithm 3], for the program. No printed source. -/
theorem holds_of_exec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F : ℕ) (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    {A par U dv : ℕ} {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : [A, par, U, dv].Nodup) (hsize : ∀ j ∈ [A, par, U, dv], j < st.store.size)
    (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0)
    (h : exec I (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run st =
      some st') :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M n F R₀ β 0 0 ⟨n, A₀, R₀, ε, ℓ₀⟩)
    pairLayout.Holds st'.store p U 0 r.1 ∧ ∀ i : Fin n, st'.store.read p dv i = some (r.2 i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hUt := hsize U (by simp)
  have hdvt := hsize dv (by simp)
  set t := st.store.size with ht
  -- the scope and the eleven allocations
  rw [eighProg_run_eq, exec_seq_skip] at h
  obtain ⟨S1, s1, hS1, -, hp1, g, he1⟩ := exists_of_exec_alloc h
  obtain ⟨S2, s2, hS2, hb2, hp2, g, he2⟩ := exists_of_exec_alloc g
  obtain ⟨S3, s3, hS3, hb3, hp3, g, he3⟩ := exists_of_exec_alloc g
  obtain ⟨S4, s4, hS4, hb4, hp4, g, he4⟩ := exists_of_exec_alloc g
  obtain ⟨S5, s5, hS5, hb5, hp5, g, he5⟩ := exists_of_exec_alloc g
  obtain ⟨S6, s6, hS6, hb6, hp6, g, he6⟩ := exists_of_exec_alloc g
  obtain ⟨S7, s7, hS7, hb7, hp7, g, he7⟩ := exists_of_exec_alloc g
  obtain ⟨S8, s8, hS8, hb8, hp8, g, he8⟩ := exists_of_exec_alloc g
  obtain ⟨S9, s9, hS9, hb9, hp9, g, he9⟩ := exists_of_exec_alloc g
  obtain ⟨S10, s10, hS10, -, hp10, g, he10⟩ := exists_of_exec_alloc g
  obtain ⟨S11, s11, hS11, -, hp11, g, he11⟩ := exists_of_exec_alloc g
  have z1 : S1.store.size = t + 1 := by rw [hS1, Array.size_push]
  have z2 : S2.store.size = t + 2 := by rw [hS2, Array.size_push, z1]
  have z3 : S3.store.size = t + 3 := by rw [hS3, Array.size_push, z2]
  have z4 : S4.store.size = t + 4 := by rw [hS4, Array.size_push, z3]
  have z5 : S5.store.size = t + 5 := by rw [hS5, Array.size_push, z4]
  have z6 : S6.store.size = t + 6 := by rw [hS6, Array.size_push, z5]
  have z7 : S7.store.size = t + 7 := by rw [hS7, Array.size_push, z6]
  have z8 : S8.store.size = t + 8 := by rw [hS8, Array.size_push, z7]
  have z9 : S9.store.size = t + 9 := by rw [hS9, Array.size_push, z8]
  have z10 : S10.store.size = t + 10 := by rw [hS10, Array.size_push, z9]
  rw [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10] at g
  -- the old buffers and the shapes of the arenas
  have a10 := storeAgree_push hS11 z10.ge
  have a9 := a10.trans (storeAgree_push hS10 z9.ge) (by omega)
  have a8 := a9.trans (storeAgree_push hS9 z8.ge) (by omega)
  have a7 := a8.trans (storeAgree_push hS8 z7.ge) (by omega)
  have a6 := a7.trans (storeAgree_push hS7 z6.ge) (by omega)
  have a5 := a6.trans (storeAgree_push hS6 z5.ge) (by omega)
  have a4 := a5.trans (storeAgree_push hS5 z4.ge) (by omega)
  have a3 := a4.trans (storeAgree_push hS4 z3.ge) (by omega)
  have a2 := a3.trans (storeAgree_push hS3 z2.ge) (by omega)
  have a1 := a2.trans (storeAgree_push hS2 z1.ge) (by omega)
  have a0 := a1.trans (storeAgree_push hS1 le_rfl) (by omega)
  simp only [IExp.eval_mul, IExp.eval_add, IExp.eval_const,
    IExp.eval_ofNat] at hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  rw [z1] at hb2
  rw [z2] at hb3
  rw [z3] at hb4
  rw [z4] at hb5
  rw [z5] at hb6
  rw [z6] at hb7
  rw [z7] at hb8
  rw [z8] at hb9
  obtain ⟨hshB, hUs, hdvs⟩ := holds_of_exec_eighProgBody hmm hqr p hflag hcmp n ℓ₀ F hn1 hlit htn
    (A₀ := A₀) (hsize A (by simp)) (hsize par (by simp)) hUt hdvt
    (fun h => by simp [h] at hbufs) hA hpar hpos (fun q b i hb => (a0 b hb).2 q i)
    (by rw [hp11, hp10, hp9, hp8, hp7, hp6, hp5, hp4, hp3, hp2, hp1])
    ((a2 (t + 1) (by omega)).1.trans hb2) ((a3 (t + 2) (by omega)).1.trans hb3)
    ((a4 (t + 3) (by omega)).1.trans hb4) ((a5 (t + 4) (by omega)).1.trans hb5)
    ((a6 (t + 5) (by omega)).1.trans hb6) ((a7 (t + 6) (by omega)).1.trans hb7)
    ((a8 (t + 7) (by omega)).1.trans hb8) ((a9 (t + 8) (by omega)).1.trans hb9) g
  -- the pops
  have hfin := read_of_eq_pop_eleven he1 he2 he3 he4 he5 he6 he7 he8 he9 he10 he11
    (by rw [Store.size_eq_of_shape_eq hshB, hS11, Array.size_push, z10])
  exact ⟨pairLayout_holds_of_read_eq hUs fun i _ _ => hfin p U i hUt,
    fun i => (hfin p dv i hdvt).trans (hdvs i)⟩

end NLAlib
