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

set_option maxHeartbeats 1600000 in
-- The invariant of the downward pass carries five facts through every level.
/-- EP1: **the downward pass**: from the initialisation (the root at depth $0$, every size cell
below it $0$, the constants and the stored $R_0$, $\beta$), the loop of
`NLAlib.eighDownLevel` over the depths $d \le \ell_0$ ends with the nodes of depth $\ell_0 + 1$ and,
for every lower depth, its nodes and records (the precise frame of
`ep2_holds_of_exec_eighDownLevel` keeps them); every cell outside the arenas and the sample
buffers is kept. -/
private theorem ep1_down_pass {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
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
  have hex' := (ep1_down_congr p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
    H.Kp c s₁).symm.trans hex
  have hcs : ∀ j, s₁.store.read p c j = σ0.store.read p c j := fun j =>
    hfr1 p c j hcH (Ne.symm hSuc) (Ne.symm hSgc)
  obtain ⟨hL2, hR2, hfr2, hsh2, hpu2, hpg2⟩ := ep2_holds_of_exec_eighDownLevel hmm hqr p hflag hcmp
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
    refine ⟨ep1_lev_tr hn1 (fun q b i hb hlc => hfr2 q b i
      (fun e => hSu (e ▸ ep1_mem3 hb)) (fun e => hSg (e ▸ ep1_mem3 hb))
      (fun h => ep1_disj hnd hb h.1)
      (fun h => by have := ep1_lc_eq hnd hlc h; omega)) hL, ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he' | rfl
    · exact ep1_rec_tr hn1 (fun q b i hb hlc => hfr2 q b i
        (fun e => hSu (e ▸ ep1_mem5 hb)) (fun e => hSg (e ▸ ep1_mem5 hb))
        (fun h => by have := ep1_lc_eq hnd hlc h.2; omega)
        (fun h => by have := ep1_lc_eq hnd hlc h; omega)) (hlow1 e he').2
    · exact hR2
  · have hlc : H.LevelCell n e H.Sz (n * e + lo) :=
      Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by rw [Nat.mul_succ]; omega⟩)
    have hSzm : H.Sz = H.Ma ∨ H.Sz = H.Sz ∨ H.Sz = H.Lv := Or.inr (Or.inl rfl)
    exact el1_readsIdx_congr (hfr2 p H.Sz (n * e + lo)
      (fun e => hSu (e ▸ ep1_mem3 hSzm)) (fun e => hSg (e ▸ ep1_mem3 hSzm))
      (fun h => ep1_disj hnd hSzm h.1)
      (fun h => by have := ep1_lc_eq hnd hlc h; omega))
      (hz1 e lo (by omega) he2 hlo)
  · refine (hfr2 q b i h1 h2 (fun h => hb ?_) (fun h => hb (ep1_lc_mem h))).trans
      (hfr1 q b i hb h1 h2)
    obtain ⟨h', -⟩ := h
    exact ep1_mem5 (by rcases h' with h | h | h | h | h <;> simp [h])

set_option maxHeartbeats 1600000 in
-- The invariant of the upward pass carries three facts through every level.
/-- EP1: **the spent level and the upward pass**: from the nodes of depth $\ell_0 + 1$ and the
nodes and records of every lower depth, `NLAlib.eighBottomLevel` and the loop of
`NLAlib.eighUpLevel` over the depths $\ell_0, \ldots, 0$ end with the outputs of depth $0$; every
cell outside the output and eigenvalue arenas is kept. -/
private theorem ep1_up_pass {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
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
    ⟨hshB, hOD, fun e he => ⟨ep1_lev_tr hn1 (fun q b i hb hlc => hfrB q b i
        (fun h => ep1_disj' hnd hb h.1)) (hlow e he).1,
      ep1_rec_tr hn1 (fun q b i hb hlc => hfrB q b i
        (fun h => by have := ep1_lc_eq hnd hlc h.2; omega)) (hlow e he).2⟩,
      fun q b i h1 h2 => hfrB q b i (fun h => h.1.elim h1 h2)⟩ ?_ h
  · obtain ⟨hsh, hO, -, hfr⟩ := hR
    change H.OutHolds σu.store p M n F (ℓ₀ + 1) R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1 - (ℓ₀ + 1)) at hO
    rw [Nat.sub_self] at hO
    exact ⟨hsh, hO, hfr⟩
  intro j hj s₁ s₂ ⟨hsh1, hO1, hlow1, hfr1⟩ hex
  change j < ℓ₀ + 1 at hj
  have hex' : exec I (eighUpLevel p mm (.const n) (.const (ℓ₀ - j)) H.Lv H.Ua H.Qa H.Ea H.Sz
      H.Kd H.Kp ⟨c, 1⟩).run s₁ = some s₂ := by
    rw [← ep1_up_congr p mm n (ℓ₀ - j) (.const ℓ₀ - .var j) rfl]
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
  exact ⟨ep1_lev_tr hn1 (fun q b i hb hlc => hfr2 q b i
      (fun h => ep1_disj' hnd hb h.1)) (hlow1 e (by omega)).1,
    ep1_rec_tr hn1 (fun q b i hb hlc => hfr2 q b i
      (fun h => by have := ep1_lc_eq hnd hlc h.2; omega)) (hlow1 e (by omega)).2⟩

omit [AddMonoid C] [Inhabited K] in
/-- EP1: a pushed store reads as before below its old size. -/
private theorem ep1_push {S S' : St P K C} {x : P × Array (Option K)}
    (h : S'.store = S.store.push x) {b : ℕ} (hb : b < S.store.size) :
    S'.store.shape[b]? = S.store.shape[b]? ∧ ∀ q i, S'.store.read q b i = S.store.read q b i := by
  rw [h]
  exact ⟨Store.getElem?_shape_push_of_lt _ hb, fun q i => Store.read_push_of_lt hb⟩

omit [AddMonoid C] [Inhabited K] in
/-- EP1: a popped store reads as before below its new size. -/
private theorem ep1_pop {s s' : Store P K} {m : ℕ} (he : s' = Array.pop s) (hs : s.size = m + 1) :
    s'.size = m ∧ ∀ q b i, b < m → s'.read q b i = s.read q b i := by
  subst he
  exact ⟨by simp [hs], fun q b i hb => Store.read_pop_of_lt (by omega)⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the handles of the program's buffers are distinct. -/
private theorem ep1_nodup {t par : ℕ} (hp : par < t) :
    ([t + 1, t + 2, t + 3, t + 4, t + 5, t + 6, t + 7, t + 8] ++
      [par, t + 9, t + 10, t]).Nodup := by
  simp
  omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the constants are not an arena. -/
private theorem ep1_notMem (t : ℕ) :
    t ∉ [t + 1, t + 2, t + 3, t + 4, t + 5, t + 6, t + 7, t + 8] := by
  simp

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the tree of `NLAlib.eighProg`, its eleven allocations and its body. -/
private theorem ep1_prog_eq (p : P) (mm qr : ι) (n ℓ₀ F A par U dv : ℕ) :
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

set_option maxHeartbeats 4000000 in
-- The run unfolds the initialisation, the two passes and the copies out.
/-- EP1: **the body of `NLAlib.eighProg`** after its eleven allocations (the constants at `t`,
the arenas at `t + 1` to `t + 8`, the samples at `t + 9`, `t + 10`): a successful run ends with
the root's output of `NLAlib.eigh` in `U` and `dv`, with the store shape kept. -/
private theorem ep1_body {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
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
  intro M r
  -- the initialisation
  obtain ⟨v0, W1, T1, hv0, hw1, hT1, hq1, g12⟩ := ep1_inv_lit h
  clear h
  obtain ⟨v1, W2, T2, hv1, hw2, hT2, hq2, g13⟩ := ep1_inv_litIdx g12
  clear g12
  obtain ⟨a2, b2, v2, W3, T3, ha2, hb2', hv2, hw3, hT3, hq3, g14⟩ := ep1_inv_bin g13
  clear g13
  obtain ⟨a3, v3, W4, T4, ha3, hv3, hw4, hT4, hq4, g15⟩ := ep1_inv_un g14
  clear g14
  obtain ⟨a4, v4, W5, T5, ha4, hv4, hw5, hT5, hq5, g16⟩ := ep1_inv_un g15
  clear g15
  obtain ⟨σ6, h6, g17⟩ := el1_seq g16
  clear g16
  obtain ⟨v7, W7, T7, hv7, hw7, hT7, hq7, g18⟩ := ep1_inv_litIdx g17
  clear g17
  obtain ⟨σ8, h8, g19⟩ := el1_seq g18
  clear g18
  obtain ⟨v9, W9, T9, hv9, hw9, hT9, hq9, g20⟩ := ep1_inv_copy g19
  clear g19
  obtain ⟨v10, W10, T10, hv10, hw10, hT10, hq10, g21⟩ := ep1_inv_copy g20
  clear g20
  obtain ⟨σd, hdown, g22⟩ := el1_seq g21
  clear g21
  obtain ⟨σb, hbot, g23⟩ := el1_seq g22
  clear g22
  obtain ⟨σu, hup, g24⟩ := el1_seq g23
  clear g23
  obtain ⟨σz, hz, g25⟩ := el1_seq g24
  clear g24
  change exec I (.seq (.loop _ _) .skip) σz = some s11 at g25
  rw [exec_seq_skip] at g25
  -- the stores of the initialisation
  have hw1' : S.store.write p t 0 v0 = some W1 := hw1
  have hw2' : W1.write p t 1 v1 = some W2 := by rw [← hT1]; exact hw2
  have hw3' : W2.write p t 2 v2 = some W3 := by rw [← hT2]; exact hw3
  have hw4' : W3.write p t 3 v3 = some W4 := by rw [← hT3]; exact hw4
  have hw5' : W4.write p t 4 v4 = some W5 := by rw [← hT4]; exact hw5
  have hw7' : σ6.store.write p (t + 5) 0 v7 = some W7 := hw7
  have hw9' : σ8.store.write p (t + 8) 0 v9 = some W9 := hw9
  have hw10' : W9.write p (t + 8) 1 v10 = some W10 := by rw [← hT9]; exact hw10
  rw [hT9] at hv10
  rw [hT2] at ha2 hb2'
  rw [hT3] at ha3
  rw [hT4] at ha4
  have hv1' : I.sem.lit p ((2 : ℕ) : ℚ) = some v1 := hv1
  have hv7' : I.sem.lit p ((n : ℕ) : ℚ) = some v7 := hv7
  obtain ⟨sh6, ps6, rd6, fr6⟩ := ep1_litIdx_loop h6
  have sh6' : σ6.store.shape = W5.shape := by rw [sh6, hT5]
  have ps6' : σ6.pos = S.pos := by rw [ps6, hq5, hq4, hq3, hq2, hq1]
  have rd6' : ∀ w < n * (ℓ₀ + 1 + 1) + 1, σ6.store.read p (t + 5) w =
      I.sem.lit p ((0 : ℕ) : ℚ) := rd6
  have fr6' : ∀ q b i, (b ≠ t + 5 ∨ n * (ℓ₀ + 1 + 1) + 1 ≤ i) →
      σ6.store.read q b i = W5.read q b i := fun q b i h => (fr6 q b i h).trans (by rw [hT5])
  -- the old buffers before the copy of A
  have hr5 : ∀ q b i, b < t → W5.read q b i = st.store.read q b i := by
    intro q b i hb
    rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw3' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl (by omega)), hold q b i hb]
  have hr7 : ∀ q b i, b < t → W7.read q b i = st.store.read q b i := by
    intro q b i hb
    rw [Store.read_of_write_eq_some_of_ne hw7' (Or.inl (by omega)),
      fr6' q b i (Or.inl (by omega)), hr5 q b i hb]
  -- the copy of A into the node arena
  have hA7 : pairLayout.Holds W7 p A (0 : IExp ℕ).eval A₀ :=
    el1_holds_keep hA fun i _ _ => hr7 p A i hAt
  have hA7' : pairLayout.Holds T7.store p A (0 : IExp ℕ).eval A₀ := by rw [hT7]; exact hA7
  obtain ⟨hM8, fr8, sh8, ps8⟩ := holds_of_exec_zcopy (st := T7) p n n (X := A) (Y := t + 1)
    (xo := 0) (yo := 0) hA7' (el1_bd_ne (by omega)) ((exec_seq_skip I _ _).trans h8)
  have fr8' : ∀ q b i, b ≠ t + 1 → σ8.store.read q b i = W7.read q b i :=
    fun q b i hb => (fr8 q b i (el1_bd_ne hb)).trans (by rw [hT7])
  have sh8' : σ8.store.shape = W7.shape := by rw [sh8, hT7]
  have ps8' : σ8.pos = σ6.pos := by rw [ps8, hq7]
  have hr10 : ∀ q b i, b ≠ t + 1 → b ≠ t + 8 → W10.read q b i = W7.read q b i := by
    intro q b i h1 h2
    rw [Store.read_of_write_eq_some_of_ne hw10' (Or.inl h2),
      Store.read_of_write_eq_some_of_ne hw9' (Or.inl h2), fr8' q b i h1]
  have hold10 : ∀ q b i, b < t → W10.read q b i = st.store.read q b i := fun q b i hb =>
    (hr10 q b i (by omega) (by omega)).trans (hr7 q b i hb)
  have hv9' : v9 = R₀ := by
    have e1 : σ8.store.read p par 0 = some R₀ := by
      rw [fr8' p par 0 (by omega), hr7 p par 0 hpart, hpar.1]
    have e2 : σ8.store.read p par 0 = some v9 := hv9
    exact Option.some_inj.mp (e2.symm.trans e1)
  have hv10' : v10 = ε := by
    have e1 : W9.read p par 1 = some ε := by
      rw [Store.read_of_write_eq_some_of_ne hw9' (Or.inl (by omega)), fr8' p par 1 (by omega),
        hr7 p par 1 hpart, hpar.2.1]
    have e2 : W9.read p par 1 = some v10 := hv10
    exact Option.some_inj.mp (e2.symm.trans e1)
  rw [hv9'] at hw9'
  rw [hv10'] at hw10'
  -- the constants
  have ha2' : a2 = v0 := by
    have e1 : W2.read p t 0 = some v0 := by
      rw [Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw1']
    have e2 : W2.read p t 0 = some a2 := ha2
    exact Option.some_inj.mp (e2.symm.trans e1)
  have hb2'' : b2 = v1 := by
    have e2 : W2.read p t 1 = some b2 := hb2'
    exact Option.some_inj.mp (e2.symm.trans (Store.read_of_write_eq_some hw2'))
  have ha3' : a3 = v0 := by
    have e1 : W3.read p t 0 = some v0 := by
      rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw1']
    have e2 : W3.read p t 0 = some a3 := ha3
    exact Option.some_inj.mp (e2.symm.trans e1)
  have ha4' : a4 = v2 := by
    have e1 : W4.read p t 2 = some v2 := by
      rw [Store.read_of_write_eq_some_of_ne hw4' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw3']
    have e2 : W4.read p t 2 = some a4 := ha4
    exact Option.some_inj.mp (e2.symm.trans e1)
  rw [ha2', hb2''] at hv2
  rw [ha3'] at hv3
  rw [ha4'] at hv4
  have hc5 : W5.read p t 0 = some v0 ∧ W5.read p t 1 = some v1 ∧ W5.read p t 2 = some v2 ∧
      W5.read p t 3 = some v3 ∧ W5.read p t 4 = some v4 := by
    refine ⟨?_, ?_, ?_, ?_, Store.read_of_write_eq_some hw5'⟩
    · rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw4' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw1']
    · rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw4' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw2']
    · rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inr (by decide)),
        Store.read_of_write_eq_some_of_ne hw4' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw3']
    · rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inr (by decide)),
        Store.read_of_write_eq_some hw4']
  have hc10 : ∀ j, W10.read p t j = W5.read p t j := fun j => by
    rw [hr10 p t j (by omega) (by omega),
      Store.read_of_write_eq_some_of_ne hw7' (Or.inl (by omega)),
      fr6' p t j (Or.inl (by omega))]
  have hcM : W10.read p t 0 = I.sem.lit p 1 ∧ W10.read p t 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      W10.read p t 2 = some (M.div M.one (M.ofNat 2)) ∧ W10.read p t 3 = some (M.neg M.one) ∧
      W10.read p t 4 = some (I.sem.sqrtHalf p) := by
    rw [hc10, hc10, hc10, hc10, hc10, hc5.1, hc5.2.1, hc5.2.2.1, hc5.2.2.2.1, hc5.2.2.2.2, hv0,
      hv1']
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · change some v2 = some ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)
      rw [hv0, hv1', Option.getD_some, Option.getD_some, hv2, Option.getD_some]
    · change some v3 = some ((I.sem.un p .neg ((I.sem.lit p 1).getD default)).getD default)
      rw [hv0, Option.getD_some, hv3, Option.getD_some]
    · unfold ScalarSem.sqrtHalf
      rw [hv0, hv1', Option.getD_some, Option.getD_some, hv2, Option.getD_some, hv4,
        Option.getD_some]
  -- the arenas and the stored state after the initialisation
  let H : EighArenas := ⟨t + 1, t + 2, t + 3, t + 4, t + 5, t + 6, t + 7, t + 8⟩
  have hHMa : H.Ma = t + 1 := rfl
  have hHUa : H.Ua = t + 2 := rfl
  have hHQa : H.Qa = t + 3 := rfl
  have hHEa : H.Ea = t + 4 := rfl
  have hHSz : H.Sz = t + 5 := rfl
  have hHKd : H.Kd = t + 6 := rfl
  have hHKp : H.Kp = t + 7 := rfl
  have hHLv : H.Lv = t + 8 := rfl
  have hbufs' : (H.handles ++ [par, t + 9, t + 10, t]).Nodup := ep1_nodup hpart
  have hnd : H.handles.Nodup := (List.nodup_append.mp hbufs').1
  have hshW : W10.shape = S.store.shape := by
    rw [Store.shape_of_write_eq_some hw10', Store.shape_of_write_eq_some hw9', sh8',
      Store.shape_of_write_eq_some hw7', sh6', Store.shape_of_write_eq_some hw5',
      Store.shape_of_write_eq_some hw4', Store.shape_of_write_eq_some hw3',
      Store.shape_of_write_eq_some hw2', Store.shape_of_write_eq_some hw1']
  have HS : ∀ s : Store P K, s.shape = S.store.shape → H.Shaped s p n (ℓ₀ + 1) := by
    intro s hs
    unfold EighArenas.Shaped
    rw [hs]
    exact ⟨hnd, hsh1, hsh2, hsh3, hsh4, hsh5, hsh6, hsh7, hsh8⟩
  have hSz10 : ∀ w, w ≠ 0 → w < n * (ℓ₀ + 1 + 1) + 1 →
      W10.read p (t + 5) w = I.sem.lit p ((0 : ℕ) : ℚ) := by
    intro w hw0 hw
    rw [hr10 p _ w (by omega) (by omega), Store.read_of_write_eq_some_of_ne hw7' (Or.inr hw0),
      rd6' w hw]
  have hSz0 : W10.read p (t + 5) 0 = I.sem.lit p ((n : ℕ) : ℚ) := by
    rw [hr10 p _ 0 (by omega) (by omega), Store.read_of_write_eq_some hw7', hv7']
  have hMa10 : pairLayout.Holds W10 p (t + 1) 0 A₀ := el1_holds_keep hM8 fun i _ _ => by
    rw [Store.read_of_write_eq_some_of_ne hw10' (Or.inl (by omega)),
      Store.read_of_write_eq_some_of_ne hw9' (Or.inl (by omega))]
  have hLv0 : W10.read p (t + 8) 0 = some R₀ := by
    rw [Store.read_of_write_eq_some_of_ne hw10' (Or.inr (by decide)),
      Store.read_of_write_eq_some hw9']
  have hLv1 : W10.read p (t + 8) 1 = some ε := Store.read_of_write_eq_some hw10'
  have hlev0 : H.LevelHolds I.sem W10 p M n F ℓ₀ R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩ 0 := by
    refine ⟨fun a lo y ha hl => ?_, fun lo hlo hno => ?_, hLv0, hLv1⟩
    · obtain rfl := List.eq_nil_of_length_eq_zero ha
      simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨el1_readsIdx hlit htn (k := n) (by omega)
        (show W10.read p (t + 5) (n * 0 + 0) = I.sem.lit p ((n : ℕ) : ℚ) by
          rw [Nat.mul_zero]; exact hSz0),
        show pairLayout.Holds W10 p (t + 1) (2 * (n * n) * 0 + 2 * n * 0) A₀ by
          rw [Nat.mul_zero, Nat.mul_zero]; exact hMa10⟩
    · have hlo0 : lo ≠ 0 := by
        rintro rfl
        exact hno [] ⟨n, A₀, R₀, ε, ℓ₀⟩ rfl rfl
      have : n ≤ n * (ℓ₀ + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
      exact el1_readsIdx hlit htn (k := 0) (by omega)
        (show W10.read p (t + 5) (n * 0 + lo) = I.sem.lit p ((0 : ℕ) : ℚ) by
          rw [Nat.mul_zero, Nat.zero_add]; exact hSz10 lo hlo0 (by omega))
  -- the downward pass
  have hT10' : T10.store.shape = S.store.shape := by rw [hT10]; exact hshW
  have hpos0 : T10.pos = st.pos := by
    rw [hq10, hq9, ps8', ps6', hposS]
  obtain ⟨hshD, hLD, hlowD, hfrD⟩ := ep1_down_pass hmm hqr p hflag hcmp n ℓ₀ F hn1 hlit htn H
    (par := par) (Su := t + 9) (Sg := t + 10) (c := t) (A₀ := A₀) (ε := ε) (σ0 := T10) hbufs'
    (fun s hs => HS s (hs.trans hT10')) (by rw [hpos0]; exact hpos) (by rw [hT10]; exact hlev0)
    (fun e lo he1 he2 hlo => by
      have h1 : n * e ≤ n * (ℓ₀ + 1) := Nat.mul_le_mul_left _ he2
      have h2 : n ≤ n * e := Nat.le_mul_of_pos_right _ he1
      have h3 : n * (ℓ₀ + 1 + 1) = n * (ℓ₀ + 1) + n := by ring
      rw [hT10]
      exact el1_readsIdx hlit htn (k := 0) (by omega) (hSz10 _ (by omega) (by omega)))
    (by rw [hT10]; exact ⟨(hold10 p par 0 hpart).trans hpar.1,
      (hold10 p par 2 hpart).trans hpar.2.2⟩)
    (by rw [hT10]; exact hcM) hdown
  -- the spent level and the upward pass
  have hbot' : exec I (eighBottomLevel (ι := ι) p (.const n) (.const (ℓ₀ + 1)) (t + 2) (t + 4)
      (t + 5)).run σd = some σb := by
    rw [← ep1_bottom_congr p n (ℓ₀ + 1) (IExp.const ℓ₀ + 1) rfl]
    exact (exec_seq_skip I _ _).trans hbot
  have htH : t ∉ H.handles := ep1_notMem t
  have hcD : σd.store.read p t 1 = I.sem.lit p ((2 : ℕ) : ℚ) := by
    rw [hfrD p t 1 htH (by omega) (by omega), hT10]; exact hcM.2.1
  obtain ⟨hshU, hO0, -⟩ := ep1_up_pass hmm p n ℓ₀ F hn1 hlit htn H (c := t) (A₀ := A₀) (ε := ε)
    hnd (fun s hs => HS s (hs.trans (hshD.trans hT10'))) htH hcD hLD hlowD hbot' hup
  -- the root's output, copied out
  obtain ⟨hU0, hE0⟩ := hO0 [] 0 ⟨n, A₀, R₀, ε, ℓ₀⟩ rfl rfl
  have hU0' : pairLayout.Holds σu.store p (t + 2) (0 : IExp ℕ).eval r.1 := by
    have e : 2 * (n * n) * 0 + 2 * n * 0 = 0 := by ring
    rw [e] at hU0
    exact hU0
  obtain ⟨hUz, frz, shz, -⟩ := holds_of_exec_zcopy (st := σu) p n n (X := t + 2) (Y := U)
    (xo := 0) (yo := 0) hU0' (el1_bd_ne (by omega)) ((exec_seq_skip I _ _).trans hz)
  obtain ⟨shc, hcp, frc⟩ := ep1_copy_loop (X := t + 4) (Y := dv) (by omega) g25
  refine ⟨shc.trans (shz.trans (hshU.trans (hshD.trans hT10'))),
    el1_holds_keep hUz fun i _ _ => frc p U i (Or.inl hUdv), fun i => ?_⟩
  rw [hcp i i.isLt, frz p (t + 4) i (el1_bd_ne (by omega))]
  have := hE0 i
  simp only [Nat.mul_zero, Nat.zero_add] at this
  exact this

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: an old index below a grown store size. -/
private theorem ep1_lt {S : St P K C} {t m k : ℕ} (h : S.store.size = t + m) (hk : k < m) :
    t + k < S.store.size := by
  rw [h]; exact Nat.add_lt_add_left hk t

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: an old handle below a grown store size. -/
private theorem ep1_lt' {S : St P K C} {t m b : ℕ} (h : S.store.size = t + m) (hb : b < t) :
    b < S.store.size := by
  rw [h]; exact lt_of_lt_of_le hb (Nat.le_add_right _ _)

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
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hAt := hsize A (by simp)
  have hpart := hsize par (by simp)
  have hUt := hsize U (by simp)
  have hdvt := hsize dv (by simp)
  have hUdv : U ≠ dv := fun h => by simp [h] at hbufs
  set t := st.store.size with ht
  -- the scope and the eleven allocations
  rw [ep1_prog_eq] at h
  rw [exec_seq_skip] at h
  obtain ⟨S1, s1, hS1, hb1, hp1, g1, he1⟩ := ep1_alloc h
  clear h
  obtain ⟨S2, s2, hS2, hb2, hp2, g2, he2⟩ := ep1_alloc g1
  clear g1
  obtain ⟨S3, s3, hS3, hb3, hp3, g3, he3⟩ := ep1_alloc g2
  clear g2
  obtain ⟨S4, s4, hS4, hb4, hp4, g4, he4⟩ := ep1_alloc g3
  clear g3
  obtain ⟨S5, s5, hS5, hb5, hp5, g5, he5⟩ := ep1_alloc g4
  clear g4
  obtain ⟨S6, s6, hS6, hb6, hp6, g6, he6⟩ := ep1_alloc g5
  clear g5
  obtain ⟨S7, s7, hS7, hb7, hp7, g7, he7⟩ := ep1_alloc g6
  clear g6
  obtain ⟨S8, s8, hS8, hb8, hp8, g8, he8⟩ := ep1_alloc g7
  clear g7
  obtain ⟨S9, s9, hS9, hb9, hp9, g9, he9⟩ := ep1_alloc g8
  clear g8
  obtain ⟨S10, s10, hS10, hb10, hp10, g10, he10⟩ := ep1_alloc g9
  clear g9
  obtain ⟨S11, s11, hS11, hb11, hp11, g11, he11⟩ := ep1_alloc g10
  clear g10
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
  have z11 : S11.store.size = t + 11 := by rw [hS11, Array.size_push, z10]
  rw [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10] at g11
  -- the old buffers and the shapes of the new ones
  have hold : ∀ q b i, b < t → S11.store.read q b i = st.store.read q b i := by
    intro q b i hb
    rw [(ep1_push hS11 (b := b) (ep1_lt' z10 hb)).2, (ep1_push hS10 (b := b) (ep1_lt' z9 hb)).2,
      (ep1_push hS9 (b := b) (ep1_lt' z8 hb)).2, (ep1_push hS8 (b := b) (ep1_lt' z7 hb)).2,
      (ep1_push hS7 (b := b) (ep1_lt' z6 hb)).2, (ep1_push hS6 (b := b) (ep1_lt' z5 hb)).2,
      (ep1_push hS5 (b := b) (ep1_lt' z4 hb)).2, (ep1_push hS4 (b := b) (ep1_lt' z3 hb)).2,
      (ep1_push hS3 (b := b) (ep1_lt' z2 hb)).2, (ep1_push hS2 (b := b) (ep1_lt' z1 hb)).2,
      (ep1_push hS1 (b := b) hb).2]
  -- the shapes of the arenas
  simp only [IExp.eval_mul, IExp.eval_add, IExp.eval_const,
    IExp.eval_ofNat] at hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  have hsh1 : S11.store.shape[t + 1]? = S2.store.shape[t + 1]? := by
    rw [(ep1_push hS11 (b := t + 1) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 1) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 1) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 1) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 1) (ep1_lt z6 (by decide))).1,
      (ep1_push hS6 (b := t + 1) (ep1_lt z5 (by decide))).1,
      (ep1_push hS5 (b := t + 1) (ep1_lt z4 (by decide))).1,
      (ep1_push hS4 (b := t + 1) (ep1_lt z3 (by decide))).1,
      (ep1_push hS3 (b := t + 1) (ep1_lt z2 (by decide))).1]
  rw [z1] at hb2
  rw [hb2] at hsh1
  have hsh2 : S11.store.shape[t + 2]? = S3.store.shape[t + 2]? := by
    rw [(ep1_push hS11 (b := t + 2) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 2) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 2) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 2) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 2) (ep1_lt z6 (by decide))).1,
      (ep1_push hS6 (b := t + 2) (ep1_lt z5 (by decide))).1,
      (ep1_push hS5 (b := t + 2) (ep1_lt z4 (by decide))).1,
      (ep1_push hS4 (b := t + 2) (ep1_lt z3 (by decide))).1]
  rw [z2] at hb3
  rw [hb3] at hsh2
  have hsh3 : S11.store.shape[t + 3]? = S4.store.shape[t + 3]? := by
    rw [(ep1_push hS11 (b := t + 3) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 3) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 3) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 3) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 3) (ep1_lt z6 (by decide))).1,
      (ep1_push hS6 (b := t + 3) (ep1_lt z5 (by decide))).1,
      (ep1_push hS5 (b := t + 3) (ep1_lt z4 (by decide))).1]
  rw [z3] at hb4
  rw [hb4] at hsh3
  have hsh4 : S11.store.shape[t + 4]? = S5.store.shape[t + 4]? := by
    rw [(ep1_push hS11 (b := t + 4) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 4) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 4) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 4) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 4) (ep1_lt z6 (by decide))).1,
      (ep1_push hS6 (b := t + 4) (ep1_lt z5 (by decide))).1]
  rw [z4] at hb5
  rw [hb5] at hsh4
  have hsh5 : S11.store.shape[t + 5]? = S6.store.shape[t + 5]? := by
    rw [(ep1_push hS11 (b := t + 5) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 5) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 5) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 5) (ep1_lt z7 (by decide))).1,
      (ep1_push hS7 (b := t + 5) (ep1_lt z6 (by decide))).1]
  rw [z5] at hb6
  rw [hb6] at hsh5
  have hsh6 : S11.store.shape[t + 6]? = S7.store.shape[t + 6]? := by
    rw [(ep1_push hS11 (b := t + 6) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 6) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 6) (ep1_lt z8 (by decide))).1,
      (ep1_push hS8 (b := t + 6) (ep1_lt z7 (by decide))).1]
  rw [z6] at hb7
  rw [hb7] at hsh6
  have hsh7 : S11.store.shape[t + 7]? = S8.store.shape[t + 7]? := by
    rw [(ep1_push hS11 (b := t + 7) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 7) (ep1_lt z9 (by decide))).1,
      (ep1_push hS9 (b := t + 7) (ep1_lt z8 (by decide))).1]
  rw [z7] at hb8
  rw [hb8] at hsh7
  have hsh8 : S11.store.shape[t + 8]? = S9.store.shape[t + 8]? := by
    rw [(ep1_push hS11 (b := t + 8) (ep1_lt z10 (by decide))).1,
      (ep1_push hS10 (b := t + 8) (ep1_lt z9 (by decide))).1]
  rw [z8] at hb9
  rw [hb9] at hsh8
  have hg : exec I (do
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
          Builder P ι ℕ ℕ Unit).run S11 = some s11 := g11
  have hS11p : S11.pos = st.pos := by
    rw [hp11, hp10, hp9, hp8, hp7, hp6, hp5, hp4, hp3, hp2, hp1]
  clear g11
  obtain ⟨hshB, hUs, hdvs⟩ := ep1_body hmm hqr p hflag hcmp n ℓ₀ F hn1 hlit htn (A₀ := A₀) hAt hpart
    hUt hdvt hUdv hA hpar hpos hold hS11p hsh1 hsh2 hsh3 hsh4 hsh5 hsh6 hsh7 hsh8 hg
  clear hg
  -- the pops
  have hs11 : s11.store.size = t + 11 := by
    rw [Store.size_eq_of_shape_eq hshB, z11]
  obtain ⟨y10, q10⟩ := ep1_pop (m := t + 10) he11 (by rw [hs11])
  obtain ⟨y9, q9⟩ := ep1_pop (m := t + 9) he10 (by rw [y10])
  obtain ⟨y8, q8⟩ := ep1_pop (m := t + 8) he9 (by rw [y9])
  obtain ⟨y7, q7⟩ := ep1_pop (m := t + 7) he8 (by rw [y8])
  obtain ⟨y6, q6⟩ := ep1_pop (m := t + 6) he7 (by rw [y7])
  obtain ⟨y5, q5⟩ := ep1_pop (m := t + 5) he6 (by rw [y6])
  obtain ⟨y4, q4⟩ := ep1_pop (m := t + 4) he5 (by rw [y5])
  obtain ⟨y3, q3⟩ := ep1_pop (m := t + 3) he4 (by rw [y4])
  obtain ⟨y2, q2⟩ := ep1_pop (m := t + 2) he3 (by rw [y3])
  obtain ⟨y1, q1⟩ := ep1_pop (m := t + 1) he2 (by rw [y2])
  obtain ⟨-, q0⟩ := ep1_pop (m := t) he1 (by rw [y1])
  have hfin : ∀ q b i, b < t → st'.store.read q b i = s11.store.read q b i := by
    intro q b i hb
    have hk : ∀ k, b < t + k := fun k => lt_of_lt_of_le hb (Nat.le_add_right _ _)
    rw [q0 q b i hb, q1 q b i (hk 1), q2 q b i (hk 2), q3 q b i (hk 3), q4 q b i (hk 4),
      q5 q b i (hk 5), q6 q b i (hk 6), q7 q b i (hk 7), q8 q b i (hk 8), q9 q b i (hk 9),
      q10 q b i (hk 10)]
  exact ⟨el1_holds_keep hUs fun i _ _ => hfin p U i hUt,
    fun i => (hfin p dv i hdvt).trans (hdvs i)⟩

end NLAlib
