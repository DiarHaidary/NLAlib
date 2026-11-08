/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownLevelSuccess
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.UpLevelSuccess
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Refinement

/-!
# The spectral bisection program computes `eigh`

The refinement of the program `NLAlib.eighProg` to the shallow `NLAlib.eigh`: (a) under kernels that
are routines on pairs, a semantics that decides flags, exact integer literals up to $n + 4$ and the
exact floor conversion, **every successful run writes exactly `NLAlib.eigh`** on the machine of the
interpretation (`NLAlib.eighTapeMachine`) with the tree of samples at the slots
(`NLAlib.holds_of_exec_eighProg`); (b) under the standard model with every value in range, $u < 1$,
$\ell_0 \ge 1$ and $\varepsilon, R_0 \ge 0$, **every run succeeds** (the sign step has the shallow
step limit, so no run fails for want of steps). Both for the builder and for the registered tree
`NLAlib.eighProg.compiled`; its counts are in
`NLAlib/Matrix/Computation/SpectralBisectionProgram/Count.lean` and `…/Weight.lean`.

## Main results

* `NLAlib.exists_exec_eighProg`: every run succeeds.
* `NLAlib.eighProg.toStmt_compiled`, `NLAlib.eighProg.holds_of_exec_compiled`,
  `NLAlib.eighProg.exists_exec_compiled`: the registered tree.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! #### Helpers of `NLAlib.exists_exec_eighProg` -/

/-- Two intervals of one length at distinct multiples are disjoint. -/
private theorem eq_of_mul_le_of_lt_mul {m e e' i : ℕ} (h1 : m * e ≤ i) (h2 : i < m * (e + 1))
    (h3 : m * e' ≤ i)
    (h4 : i < m * (e' + 1)) : e = e' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := Nat.mul_le_mul_left m (show e + 1 ≤ e' by omega); omega
  · have := Nat.mul_le_mul_left m (show e' + 1 ≤ e by omega); omega

/-- The cells of distinct depths are distinct. -/
private theorem not_levelCell_of_ne {H : EighArenas} (hnd : H.handles.Nodup) {n e e' b i : ℕ}
    (hne : e ≠ e')
    (h : H.LevelCell n e b i) : ¬ H.LevelCell n e' b i := by
  intro h'
  unfold EighArenas.LevelCell at h h'
  rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1⟩ <;>
    rcases h' with ⟨hb', h1', h2'⟩ | ⟨hb', h1', h2'⟩ | ⟨hb', h1'⟩
  · exact hne (eq_of_mul_le_of_lt_mul (m := 2 * (n * n)) h1 h2 h1' h2')
  · rcases hb with rfl | rfl | rfl <;> rcases hb' with h | h | h | h <;>
      simp [EighArenas.handles, h] at hnd
  · rcases hb with rfl | rfl | rfl <;> simp [EighArenas.handles, hb'] at hnd
  · rcases hb with rfl | rfl | rfl | rfl <;> rcases hb' with h | h | h <;>
      simp [EighArenas.handles, h] at hnd
  · exact hne (eq_of_mul_le_of_lt_mul (m := n) h1 h2 h1' h2')
  · rcases hb with rfl | rfl | rfl | rfl <;> simp [EighArenas.handles, hb'] at hnd
  · subst hb; rcases hb' with h | h | h <;> simp [EighArenas.handles, h] at hnd
  · subst hb; rcases hb' with h | h | h | h <;> simp [EighArenas.handles, h] at hnd
  · omega

/-- The cells $0$ to $4$ of `c` hold the constants of `NLAlib.eighProg` (one, $\mathrm{fl}(2)$,
$\mathrm{fl}(1/2)$, $-1$, the stored $\sqrt{1/2}$). -/
private def EighConsts (I : Interp P ι K C) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K))
    (s : Store P K) (p : P) (c : ℕ) : Prop :=
  s.read p c 0 = I.sem.lit p 1 ∧ s.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
    s.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
      (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
    s.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg (eighTapeMachine I p mmR qrR).one) ∧
    s.read p c 4 = some (I.sem.sqrtHalf p)

omit [AddMonoid C] in
/-- The constants are kept by a store that reads as `s` on `c`. -/
private theorem EighConsts.of_read_eq {s s' : Store P K} {p : P} {c : ℕ}
    (hs : ∀ i, s'.read p c i = s.read p c i) (h : EighConsts I mmR qrR s p c) :
    EighConsts I mmR qrR s' p c := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨(hs 0).trans h0, (hs 1).trans h1, (hs 2).trans h2, (hs 3).trans h3, (hs 4).trans h4⟩

/-- A buffer outside the arenas is not one of them. -/
private theorem not_mem_handles_of_mem {H : EighArenas} {l : List ℕ} (h : (H.handles ++ l).Nodup)
    {x : ℕ}
    (hx : x ∈ l) : x ∉ H.handles := fun hm => List.disjoint_of_nodup_append h hm hx

/-- The sizes, node matrices and parameters are not records. -/
private theorem not_record_arena_of_node_arena {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (hb : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) :
    ¬ (b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) := by
  intro h
  rcases hb with rfl | rfl | rfl <;> rcases h with h | h | h | h | h <;>
    simp [EighArenas.handles, h] at hnd

/-- The size cell $ne$ is not a cell of a deeper depth. -/
private theorem not_levelCell_sz {H : EighArenas} (hnd : H.handles.Nodup) {n e d : ℕ} (he : e < d) :
    ¬ H.LevelCell n d H.Sz (n * e) := by
  unfold EighArenas.LevelCell
  rintro (⟨hb, -⟩ | ⟨-, h1, h2⟩ | ⟨hb, -⟩)
  · rcases hb with h | h | h <;> simp [EighArenas.handles, h] at hnd
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at h2
    · have := Nat.mul_le_mul_left n (show e + 1 ≤ d by omega)
      have : n * (e + 1) = n * e + n := by ring
      omega
  · simp [EighArenas.handles, hb] at hnd

/-- A size cell at or past depth $d + 1$ is not a cell of depth $d$. -/
private theorem not_levelCell_sz_of_le {H : EighArenas} (hnd : H.handles.Nodup) {n d j : ℕ}
    (hj : n * (d + 1) ≤ j) : ¬ H.LevelCell n d H.Sz j := by
  unfold EighArenas.LevelCell
  rintro (⟨hb, -⟩ | ⟨-, h1, h2⟩ | ⟨hb, -⟩)
  · rcases hb with h | h | h <;> simp [EighArenas.handles, h] at hnd
  · omega
  · simp [EighArenas.handles, hb] at hnd

/-- A cell the node transfer reads is not a cell of a deeper depth. -/
private theorem not_levelCell_of_lt {H : EighArenas} (hnd : H.handles.Nodup) {n e d b i : ℕ}
    (he : e < d)
    (hi : H.LevelCell n e b i ∨ (b = H.Sz ∧ i = n * e)) : ¬ H.LevelCell n d b i := by
  rcases hi with hi | ⟨rfl, rfl⟩
  · exact not_levelCell_of_ne hnd (by omega) hi
  · exact not_levelCell_sz hnd he

omit [Inhabited K] in
/-- A builder that emits one statement, then the rest, succeeds when both parts do. -/
private theorem exists_exec_bind_of_exec {b : Builder P ι ℕ ℕ Unit} {X : Stmt P ι ℕ ℕ}
    {f : Unit → Builder P ι ℕ ℕ Unit} {st s₁ : St P K C} (h₁ : exec I b.run st = some s₁)
    (h₂ : ∃ st', exec I (f ()).run s₁ = some st') (hb : ∀ k, ContT.run b k = .seq X (k ())) :
    ∃ st', exec I (b >>= f).run st = some st' := by
  rw [exec_run_bind I hb f st, h₁, Option.bind_some]
  exact h₂

/-- The downward pass succeeds and ends with the nodes of every depth $\le \ell_0 + 1$ and the
records of every depth $\le \ell_0$; the shape and every cell outside the arenas and the sample
buffers are kept. -/
private theorem exists_exec_eighDownLoop {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (hℓ : 1 ≤ ℓ₀)
    (H : EighArenas) {par Su Sg c : ℕ} {σ : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hH : H.Shaped σ.store p n (ℓ₀ + 1)) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ 0)
    (hz : ∀ j, n ≤ j → j < n * (ℓ₀ + 1 + 1) → ReadsIdx I.sem σ.store p H.Sz j 0)
    (hpos : σ.pos .uniform = 0 ∧ σ.pos .gaussian = 0)
    (hpar : σ.store.read p par 0 = some R₀ ∧ σ.store.read p par 2 = some β)
    (hSu : ∃ len, σ.store.shape[Su]? = some (p, len) ∧ n ≤ len)
    (hSg : ∃ len, σ.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len)
    (hc : EighConsts I mmR qrR σ.store p c) :
    ∃ σ' : St P K C, exec I (.loop (IExp.const ℓ₀ + 1) fun d => (eighDownLevel p mm qr (.const n)
        (.const ℓ₀) (.const F) (.var d) par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩
        ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run) σ = some σ' ∧
      σ'.store.shape = σ.store.shape ∧
      (∀ q b i, b ∉ H.handles → b ≠ Su → b ≠ Sg → σ'.store.read q b i = σ.store.read q b i) ∧
      (∀ e ≤ ℓ₀ + 1, H.LevelHolds I.sem σ'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ e < ℓ₀ + 1, H.RecordHolds I.sem σ'.store p (eighTapeMachine I p mmR qrR) n F R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) := by
  have hnd := hH.1
  have hflag : I.sem.DecidesFlags p := hsem.decidesFlags (fun q k hk => hlit q k (hk.trans
      (by omega))) p
  have hcmp := hsem.cmp_le p
  have hpo := not_mem_handles_of_mem hbufs (x := par) (by simp)
  have hco := not_mem_handles_of_mem hbufs (x := c) (by simp)
  have dSuSg : Su ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSu : par ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSg : par ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSu : c ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSg : c ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have hSuo := not_mem_handles_of_mem hbufs (x := Su) (by simp)
  have hSgo := not_mem_handles_of_mem hbufs (x := Sg) (by simp)
  have hhS : ∀ {b}, b ∈ H.handles → b ≠ Su ∧ b ≠ Sg := fun hb =>
    ⟨fun h => hSuo (h ▸ hb), fun h => hSgo (h ▸ hb)⟩
  have hmsl : ∀ {b}, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → b ∈ H.handles := fun hb => by
    rcases hb with rfl | rfl | rfl <;> simp [EighArenas.handles]
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := IExp.const ℓ₀ + 1)
    (fun d (s : St P K C) => s.store.shape = σ.store.shape ∧ s.pos .uniform = n * d ∧
      s.pos .gaussian = 4 * (n * n) * d ∧
      (∀ q b i, b ∉ H.handles → b ≠ Su → b ≠ Sg → s.store.read q b i = σ.store.read q b i) ∧
      (∀ e ≤ d, H.LevelHolds I.sem s.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ e < d, H.RecordHolds I.sem s.store p (eighTapeMachine I p mmR qrR) n F R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      ∀ j, n * (d + 1) ≤ j → j < n * (ℓ₀ + 1 + 1) → ReadsIdx I.sem s.store p H.Sz j 0)
    ⟨rfl, by rw [hpos.1]; ring, by rw [hpos.2]; ring, fun _ _ _ _ _ _ => rfl,
      fun e he => by obtain rfl : e = 0 := (by omega); exact hlev,
      fun e he => absurd he (Nat.not_lt_zero _), fun j hj => hz j (by simpa using hj)⟩ ?_).elim
    fun σ' h => ⟨σ', h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  rintro d hd s ⟨hsh, hpu, hpg, hfr, hlv, hrc, hzs⟩
  change d < ℓ₀ + 1 at hd
  have hHs : H.Shaped s.store p n (ℓ₀ + 1) :=
    EighArenas.Shaped.of_shape_eq (fun b _ => by rw [hsh]) hH
  have hpar' : s.store.read p par 0 = some R₀ ∧ s.store.read p par 2 = some β :=
    ⟨(hfr _ _ _ hpo dparSu dparSg).trans hpar.1, (hfr _ _ _ hpo dparSu dparSg).trans hpar.2⟩
  have hcs : EighConsts I mmR qrR s.store p c :=
    EighConsts.of_read_eq (fun i => hfr _ _ _ hco dcSu dcSg) hc
  have hSu' : ∃ len, s.store.shape[Su]? = some (p, len) ∧ n ≤ len := by rw [hsh]; exact hSu
  have hSg' : ∃ len, s.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len := by
    rw [hsh]; exact hSg
  obtain ⟨s', hs'⟩ := exists_exec_eighDownLevel hmm hqr hsem p hu n ℓ₀ F d (ℓ₀ + 1) hd hℓ hlit
    htn H hε hR₀ hHs hbufs (hlv d le_rfl) hpar' hSu' hSg' ⟨hpu, hpg⟩ hcs
  have hnext : ∀ lo < n, ReadsIdx I.sem s.store p H.Sz (n * (d + 1) + lo) 0 := fun lo hlo =>
    hzs _ (by omega) (by
      have := Nat.mul_le_mul_left n (show d + 1 + 1 ≤ ℓ₀ + 1 + 1 by omega)
      have : n * (d + 1 + 1) = n * (d + 1) + n := by ring
      omega)
  obtain ⟨L1, R1, F1, S1, P1, P2⟩ := levelHolds_succ_of_exec_eighDownLevel hmm hqr p hflag hcmp n ℓ₀
    F d (ℓ₀ + 1) hlit htn H hHs hbufs (hlv d le_rfl) hnext ⟨hpu, hpg⟩ hpar' hcs hs'
  refine ⟨s', (exec_eighDownLevel_var p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c
    s).trans hs', S1.trans hsh, by rw [P1, hpu]; ring, by rw [P2, hpg]; ring,
    fun q b i hb h1 h2 => ?_, fun e he => ?_, fun e he => ?_, fun j hj1 hj2 => ?_⟩
  · exact (F1 q b i h1 h2 (fun h => hb (mem_handles_of_levelCell h.2)) (fun h => hb
      (mem_handles_of_levelCell h))).trans
      (hfr q b i hb h1 h2)
  · rcases Nat.lt_or_ge e (d + 1) with he' | he'
    · refine EighArenas.LevelHolds.of_read_eq (fun q b i hb hi => F1 q b i (hhS (hmsl hb)).1
        (hhS (hmsl hb)).2 (fun h => not_record_arena_of_node_arena hnd hb h.1)
            (not_levelCell_of_lt hnd he' hi)) (hlv e (by omega))
    · obtain rfl : e = d + 1 := by omega
      exact L1
  · rcases Nat.lt_or_ge e d with he' | he'
    · refine EighArenas.RecordHolds.of_read_eq (fun q b i _ hi => F1 q b i
        (hhS (mem_handles_of_levelCell hi)).1 (hhS (mem_handles_of_levelCell hi)).2
            (fun h => not_levelCell_of_ne hnd (by omega) hi h.2)
        (not_levelCell_of_ne hnd (by omega) hi)) (hrc e he')
    · obtain rfl : e = d := by omega
      exact R1
  · have hSzh : H.Sz ∈ H.handles := hmsl (Or.inr (Or.inl rfl))
    refine readsIdx_of_read_eq (F1 p H.Sz j (hhS hSzh).1 (hhS hSzh).2
      (fun h => not_record_arena_of_node_arena hnd (Or.inr (Or.inl rfl)) h.1)
          (not_levelCell_sz_of_le hnd hj1)) (hzs j ?_ hj2)
    have := Nat.mul_le_mul_left n (show d + 1 ≤ d + 1 + 1 by omega)
    omega

/-- The upward pass succeeds and ends with the outputs of depth $0$; the shape and every
cell outside the arenas are kept. -/
private theorem exists_exec_eighUpLoop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {c : ℕ} {σ : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped σ.store p n (ℓ₀ + 1)) (hco : c ∉ H.handles)
    (htwov : σ.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : ∀ e < ℓ₀ + 1, H.LevelHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ e)
    (hrec : ∀ e < ℓ₀ + 1, H.RecordHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ e)
    (hout : H.OutHolds σ.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ (ℓ₀ + 1)) :
    ∃ σ' : St P K C, exec I (.loop (IExp.const ℓ₀ + 1) fun j => (eighUpLevel p mm (.const n)
        (.const ℓ₀ - .var j) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 1⟩).run) σ = some σ' ∧
      σ'.store.shape = σ.store.shape ∧
      (∀ q b i, b ∉ H.handles → σ'.store.read q b i = σ.store.read q b i) ∧
      H.OutHolds σ'.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ 0 := by
  have hnd := hH.1
  have hmsl : ∀ {b}, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → ¬ (b = H.Ua ∨ b = H.Ea) :=
    fun hb h => not_record_arena_of_node_arena hnd hb (h.elim (fun h => Or.inr (Or.inl h))
      (fun h => Or.inr (Or.inr (Or.inl h))))
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := IExp.const ℓ₀ + 1)
    (fun j (s : St P K C) => s.store.shape = σ.store.shape ∧
      (∀ q b i, b ∉ H.handles → s.store.read q b i = σ.store.read q b i) ∧
      (∀ e < ℓ₀ + 1 - j, H.LevelHolds I.sem s.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      (∀ e < ℓ₀ + 1 - j, H.RecordHolds I.sem s.store p (eighTapeMachine I p mmR qrR) n F R₀ β
        ⟨n, A₀, R₀, ε, ℓ₀⟩ e) ∧
      H.OutHolds s.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β ⟨n, A₀, R₀, ε, ℓ₀⟩
        (ℓ₀ + 1 - j))
    ⟨rfl, fun _ _ _ _ => rfl, hlev, hrec, hout⟩ ?_).elim
    fun σ' h => ⟨σ', h.1, h.2.1, h.2.2.1, by
      have h5 := h.2.2.2.2.2
      rwa [show (IExp.const ℓ₀ + 1 : IExp ℕ).eval = ℓ₀ + 1 from rfl, Nat.sub_self] at h5⟩
  rintro j hj s ⟨hsh, hfr, hlv, hrc, hot⟩
  change j < ℓ₀ + 1 at hj
  have e1 : ℓ₀ + 1 - j = ℓ₀ - j + 1 := by omega
  have e2 : ℓ₀ + 1 - (j + 1) = ℓ₀ - j := by omega
  rw [e1] at hlv hrc hot
  rw [e2]
  have hHs : H.Shaped s.store p n (ℓ₀ + 1) := EighArenas.Shaped.of_shape_eq (fun b _ => by rw [hsh])
      hH
  have htw : s.store.read p (⟨c, 1⟩ : Cell ℕ ℕ).buf (⟨c, 1⟩ : Cell ℕ ℕ).idx.eval =
      I.sem.lit p ((2 : ℕ) : ℚ) := (hfr p c 1 hco).trans htwov
  obtain ⟨s', hs'⟩ := exists_exec_eighUpLevel hmm hsem p n ℓ₀ F (ℓ₀ - j) (ℓ₀ + 1) (by omega)
    hlit htn H (two := ⟨c, 1⟩) hHs hco htw (hlv _ (by omega)) (hrc _ (by omega)) hot
  obtain ⟨O1, F1, S1, -⟩ := holds_of_exec_eighUpLevel hmm p n ℓ₀ F (ℓ₀ - j) (ℓ₀ + 1) (by omega)
    hlit htn H (two := ⟨c, 1⟩) hHs hco htw (hlv _ (by omega)) (hrc _ (by omega)) hot hs'
  refine ⟨s', (exec_eighUpLevel_of_eval_eq p mm n (ℓ₀ - j) _ rfl H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
      c s).trans hs',
    S1.trans hsh, fun q b i hb => (F1 q b i fun h => hb (mem_handles_of_levelCell h.2)).trans
        (hfr q b i hb),
    fun e he => EighArenas.LevelHolds.of_read_eq (fun q b i hb _ => F1 q b i fun h => hmsl hb h.1)
      (hlv e (by omega)),
    fun e he => EighArenas.RecordHolds.of_read_eq
      (fun q b i _ hi => F1 q b i fun h => not_levelCell_of_ne hnd (by omega) hi h.2) (hrc e
          (by omega)), O1⟩

/-- From the initialised arenas, the two passes, the spent level and the final copies of
`NLAlib.eighProg` succeed. -/
private theorem exists_exec_eighPasses {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (hℓ : 1 ≤ ℓ₀)
    (H : EighArenas) {par Su Sg c U dv : ℕ} {σ : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hH : H.Shaped σ.store p n (ℓ₀ + 1)) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hUo : U ∉ H.handles) (hdvo : dv ∉ H.handles)
    (hlev : H.LevelHolds I.sem σ.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ 0)
    (hz : ∀ j, n ≤ j → j < n * (ℓ₀ + 1 + 1) → ReadsIdx I.sem σ.store p H.Sz j 0)
    (hpos : σ.pos .uniform = 0 ∧ σ.pos .gaussian = 0)
    (hpar : σ.store.read p par 0 = some R₀ ∧ σ.store.read p par 2 = some β)
    (hSu : ∃ len, σ.store.shape[Su]? = some (p, len) ∧ n ≤ len)
    (hSg : ∃ len, σ.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len)
    (hc : EighConsts I mmR qrR σ.store p c)
    (hU : ∃ len, σ.store.shape[U]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hdv : ∃ len, σ.store.shape[dv]? = some (p, len) ∧ n ≤ len) :
    ∃ st', exec I (Builder.run (ι := ι) (do
      forRange (IExp.const ℓ₀ + 1) fun d =>
        eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par H.Lv Su Sg H.Ma H.Ua
          H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
      eighBottomLevel p (.const n) (IExp.const ℓ₀ + 1) H.Ua H.Ea H.Sz
      forRange (IExp.const ℓ₀ + 1) fun d' =>
        eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 1⟩
      zcopy p (.const n) (.const n) H.Ua 0 U 0
      forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨H.Ea, .var i⟩))) σ = some st' := by
  have hnd := hH.1
  have hco := not_mem_handles_of_mem hbufs (x := c) (by simp)
  have dcSu : c ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSg : c ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have hmsl : ∀ {b}, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → ¬ (b = H.Ua ∨ b = H.Ea) :=
    fun hb h => not_record_arena_of_node_arena hnd hb (h.elim (fun h => Or.inr (Or.inl h))
      (fun h => Or.inr (Or.inr (Or.inl h))))
  have hUUa : U ≠ H.Ua := fun h => hUo (h ▸ by simp [EighArenas.handles])
  have hEaU : H.Ea ≠ U := fun h => hUo (h ▸ by simp [EighArenas.handles])
  have hEadv : H.Ea ≠ dv := fun h => hdvo (h ▸ by simp [EighArenas.handles])
  -- the downward pass
  obtain ⟨σ2, h2, hsh2, hfr2, hlv2, hrc2⟩ := exists_exec_eighDownLoop hmm hqr hsem p hu n ℓ₀ F hlit
      htn hℓ H hε
    hR₀ hH hbufs hlev hz hpos hpar hSu hSg hc
  refine exists_exec_bind_of_exec (by exact (exec_seq_skip I _ _).trans h2) ?_ (by intro _; rfl)
  -- the spent level
  have hH2 : H.Shaped σ2.store p n (ℓ₀ + 1) := EighArenas.Shaped.of_shape_eq
      (fun b _ => by rw [hsh2]) hH
  obtain ⟨σb, hb⟩ := exists_exec_eighBottomLevel (ι := ι) hsem htn p n ℓ₀ F (ℓ₀ + 1) H hH2
    (hlv2 _ le_rfl)
  obtain ⟨Ob, Fb, Sb, -⟩ := holds_of_exec_eighBottomLevel p n ℓ₀ F (ℓ₀ + 1) hlit htn H hH2
    (hlv2 _ le_rfl) hb
  refine exists_exec_bind_of_exec
    (by exact (exec_eighBottomLevel_of_eval_eq p n (ℓ₀ + 1) _ rfl H.Ua H.Ea H.Sz σ2).trans hb) ?_
    (by intro _; rfl)
  -- the upward pass
  have hHb : H.Shaped σb.store p n (ℓ₀ + 1) := EighArenas.Shaped.of_shape_eq (fun b _ => by rw [Sb])
      hH2
  obtain ⟨σ3, h3, hsh3, -, hout3⟩ := exists_exec_eighUpLoop hmm hsem p n ℓ₀ F hlit htn H hHb hco
    ((Fb p c 1 fun h => hco (mem_handles_of_levelCell h.2)).trans
        ((hfr2 p c 1 hco dcSu dcSg).trans hc.2.1))
    (fun e he => EighArenas.LevelHolds.of_read_eq (fun q b i hb _ => Fb q b i fun h => hmsl hb h.1)
      (hlv2 e (by omega)))
    (fun e he => EighArenas.RecordHolds.of_read_eq
      (fun q b i _ hi => Fb q b i fun h => not_levelCell_of_ne hnd (by omega) hi h.2) (hrc2 e he))
          Ob
  refine exists_exec_bind_of_exec (by exact (exec_seq_skip I _ _).trans h3) ?_ (by intro _; rfl)
  -- the copies of the root's output
  have hroot := hout3 [] 0 ⟨n, A₀, R₀, ε, ℓ₀⟩ rfl rfl
  have hU0 := hroot.1
  simp only [Nat.mul_zero, Nat.add_zero] at hU0
  have hsh3' : σ3.store.shape = σ.store.shape := hsh3.trans (Sb.trans hsh2)
  obtain ⟨len, hUs, hUlen⟩ := hU
  obtain ⟨σ4, h4⟩ := exists_exec_zcopy (ι := ι) p n n (X := H.Ua) (xo := 0) (Y := U) (yo := 0)
    hU0 (blockDisjoint_of_ne hUUa) ⟨len,
        by rw [hsh3']; exact hUs, by change 0 + 2 * (n * n) ≤ len; omega⟩
  obtain ⟨-, F4, S4, -⟩ := holds_of_exec_zcopy p n n hU0 (blockDisjoint_of_ne hUUa) h4
  refine exists_exec_bind_of_exec (by exact h4) ?_ (by intro _; rfl)
  obtain ⟨ldv, hdvs, hdvlen⟩ := hdv
  have hstep : ∀ i < (IExp.const n).eval, ∀ s : St P K C,
      (s.store.shape = σ4.store.shape ∧
        ∀ i, s.store.read p H.Ea i = σ4.store.read p H.Ea i) →
      ∃ s', exec I (Builder.ins (ι := ι) (.copy p ⟨dv, .var i⟩ ⟨H.Ea, .var i⟩)).run s = some s' ∧
        (s'.store.shape = σ4.store.shape ∧
          ∀ i, s'.store.read p H.Ea i = σ4.store.read p H.Ea i) := by
    rintro i hi s ⟨hsh, hE⟩
    change i < n at hi
    obtain ⟨v, hv⟩ : ∃ v, s.store.read p H.Ea i = some v := by
      have := hroot.2 ⟨i, hi⟩
      simp only [Nat.mul_zero, Nat.zero_add] at this
      exact ⟨_, (hE i).trans ((F4 p H.Ea i (blockDisjoint_of_ne hEaU)).trans this)⟩
    obtain ⟨s', hw⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := i) v
      (by rw [hsh, S4, hsh3']; exact hdvs) (by omega)
    refine ⟨_, (exec_seq_instr_copy I (dst := ⟨dv, .var i⟩) (src := ⟨H.Ea, .var i⟩) hv hw).trans
      (exec_skip I _), (Store.shape_of_write_eq_some hw).trans hsh, fun j => ?_⟩
    exact (Store.read_of_write_eq_some_of_ne hw (Or.inl hEadv)).trans (hE j)
  obtain ⟨σ5, h5, -⟩ := exists_exec_loop_eq_some_of_forall (I := I) _ ⟨rfl, fun _ => rfl⟩ hstep
  exact ⟨σ5, (exec_seq_skip I _ _).trans h5⟩

omit [Inhabited K] in
/-- A literal, then the rest. -/
private theorem exists_exec_seq_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {v : K} {s' : Store P K} (hv : I.sem.lit p q = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some st') :
    ∃ st', exec I (.seq (.instr (.lit p dst q)) t) s = some st' := by
  rw [exec_seq_instr_lit I hv hw]
  exact h

omit [Inhabited K] in
/-- A unary operation, then the rest. -/
private theorem exists_exec_seq_un {p : P} {o : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {a v : K} {s' : Store P K} (hx : s.store.read p x.buf x.idx.eval = some a)
    (hv : I.sem.un p o a = some v) (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.un p o) } = some st') :
    ∃ st', exec I (.seq (.instr (.un p o dst x)) t) s = some st' := by
  rw [exec_seq_instr_un I hx hv hw]
  exact h

omit [Inhabited K] in
/-- A copy, then the rest. -/
private theorem exists_exec_seq_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {v : K} {s' : Store P K} (hx : s.store.read p src.buf src.idx.eval = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.copy p) } = some st') :
    ∃ st', exec I (.seq (.instr (.copy p dst src)) t) s = some st' := by
  rw [exec_seq_instr_copy I hx hw]
  exact h

omit [Inhabited K] in
/-- A loop writing the index literal $0$ into the first cells of a buffer succeeds; those
cells hold it, and the shape, the tape positions and the other buffers are kept. -/
private theorem exists_exec_loop_litIdx {p : P} {m : IExp ℕ} {Y len : ℕ} {z : K} {st : St P K C}
    (hz : I.sem.lit p (((0 : IExp ℕ).eval : ℕ) : ℚ) = some z)
    (hY : st.store.shape[Y]? = some (p, len)) (hm : m.eval ≤ len) :
    ∃ st' : St P K C, exec I (.loop m fun w =>
        (Builder.ins (ι := ι) (.litIdx p ⟨Y, .var w⟩ 0)).run) st = some st' ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ j < m.eval, st'.store.read p Y j = some z) ∧
      ∀ q b i, b ≠ Y → st'.store.read q b i = st.store.read q b i := by
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := m)
    (fun w (s : St P K C) => s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
      (∀ j < w, s.store.read p Y j = some z) ∧
      ∀ q b i, b ≠ Y → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_).elim
    fun σ' h => ⟨σ', h.1, h.2⟩
  rintro w hw s ⟨hsh, hps, hY', hfr⟩
  obtain ⟨s', hw'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := w) z (hsh ▸ hY)
    (by omega)
  refine ⟨_, (exec_seq_instr_litIdx I (dst := ⟨Y, .var w⟩) (e := 0) hz hw').trans
    (exec_skip I _), (Store.shape_of_write_eq_some hw').trans hsh, hps, fun j hj => ?_,
    fun q b i hb => (Store.read_of_write_eq_some_of_ne hw' (Or.inl hb)).trans (hfr q b i hb)⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact (Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega))).trans (hY' j hj)
  · exact Store.read_of_write_eq_some hw'

/-- The constants of `NLAlib.eighProg`: under the standard model at $u$ with $u(p) < 1$ and exact
integer literals up to $B \ge 2$, the five instructions writing one, $\mathrm{fl}(2)$,
$\mathrm{fl}(1/2)$, $-1$ and $\sqrt{1/2}$ into a buffer `c` of five cells succeed, and the rest
succeeds when it does from every state at the same tape positions and shape whose buffer `c`
holds the constants (`EighConsts`) and whose other buffers read as at the start. -/
private theorem exists_exec_consts {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) {B : ℕ}
    (hlit : IsExactIntLit dec I.sem B) (hB : 2 ≤ B) {c : ℕ} {σ : St P K C}
    (hsc : σ.store.shape[c]? = some (p, 5)) {t : Builder P ι ℕ ℕ Unit}
    (ht : ∀ σ' : St P K C, EighConsts I mmR qrR σ'.store p c → σ'.store.shape = σ.store.shape →
      (∀ q b i, b ≠ c → σ'.store.read q b i = σ.store.read q b i) → σ'.pos = σ.pos →
      ∃ st', exec I t.run σ' = some st') :
    ∃ st', exec I (Builder.run (ι := ι) (do
      ins (.lit p ⟨c, 0⟩ 1)
      ins (.litIdx p ⟨c, 1⟩ 2)
      ins (.bin p .div ⟨c, 2⟩ ⟨c, 0⟩ ⟨c, 1⟩)
      ins (.un p .neg ⟨c, 3⟩ ⟨c, 0⟩)
      ins (.un p .sqrt ⟨c, 4⟩ ⟨c, 2⟩)
      t)) σ = some st' := by
  -- the values of the constants
  obtain ⟨o, ho, ho1⟩ := hlit p 1 (by omega)
  have ho' : I.sem.lit p 1 = some o := by simpa using ho
  obtain ⟨tw, htw, htw2⟩ := hlit p 2 hB
  obtain ⟨hf, hfh, δ, hδ, hfd⟩ := exists_bin_eq_some hsem p (b := .div) trivial (x := o) (y := tw)
    (fun _ => by rw [htw2]; norm_num)
  obtain ⟨ng, hng, -⟩ := hsem.neg p o
  have hf0 : 0 ≤ dec p hf := by
    rw [hfd, ho1, htw2]
    have := (abs_le.mp hδ).1
    simp only [BinOp.realOp]
    apply mul_nonneg (by positivity)
    linarith
  obtain ⟨sq, hsq⟩ := hsem.sqrt_ok p hf hf0
  -- the writes
  obtain ⟨S1, w1⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) o hsc (by norm_num)
  have sh1 := Store.shape_of_write_eq_some w1
  obtain ⟨S2, w2⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) tw
    (by rw [sh1]; exact hsc) (by norm_num)
  have sh2 := (Store.shape_of_write_eq_some w2).trans sh1
  obtain ⟨S3, w3⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 2) hf
    (by rw [sh2]; exact hsc) (by norm_num)
  have sh3 := (Store.shape_of_write_eq_some w3).trans sh2
  obtain ⟨S4, w4⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 3) ng
    (by rw [sh3]; exact hsc) (by norm_num)
  have sh4 := (Store.shape_of_write_eq_some w4).trans sh3
  obtain ⟨S5, w5⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 4) sq
    (by rw [sh4]; exact hsc) (by norm_num)
  have sh5 := (Store.shape_of_write_eq_some w5).trans sh4
  have r20 : S2.read p c 0 = some o :=
    (Store.read_of_write_eq_some_of_ne w2 (Or.inr (by omega))).trans
      (Store.read_of_write_eq_some w1)
  have r30 : S3.read p c 0 = some o :=
    (Store.read_of_write_eq_some_of_ne w3 (Or.inr (by omega))).trans r20
  have r21 : S2.read p c 1 = some tw := Store.read_of_write_eq_some w2
  have r42 : S4.read p c 2 = some hf :=
    (Store.read_of_write_eq_some_of_ne w4 (Or.inr (by omega))).trans
      (Store.read_of_write_eq_some w3)
  refine exists_exec_seq_lit (by exact ho') (by exact w1) ?_
  refine exists_exec_seq_litIdx (by exact htw) (by exact w2) ?_
  refine exists_exec_seq_bin (by exact r20) (by exact r21) hfh (by exact w3) ?_
  refine exists_exec_seq_un (by exact r30) hng (by exact w4) ?_
  refine exists_exec_seq_un (by exact r42) hsq (by exact w5) ?_
  refine exists_exec_of_forall_eq fun σ5 hσ5 => ?_
  have h5s : σ5.store = S5 := by rw [hσ5]
  refine ht σ5 ?_ (by rw [h5s, sh5]) (fun q b i hb => ?_) (by rw [hσ5])
  · rw [h5s]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Store.read_of_write_eq_some_of_ne w5 (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne w4 (Or.inr (by omega)), r30, ho']
    · rw [Store.read_of_write_eq_some_of_ne w5 (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne w4 (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne w3 (Or.inr (by omega)), r21, htw]
    · rw [Store.read_of_write_eq_some_of_ne w5 (Or.inr (by omega)), r42]
      change some hf = some ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)
      rw [ho', htw]
      simp [hfh]
    · rw [Store.read_of_write_eq_some_of_ne w5 (Or.inr (by omega)), Store.read_of_write_eq_some w4]
      change some ng = some ((I.sem.un p .neg ((I.sem.lit p 1).getD default)).getD default)
      rw [ho']
      simp [hng]
    · rw [Store.read_of_write_eq_some w5]
      change some sq = some ((I.sem.un p .sqrt ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)).getD default)
      rw [ho', htw]
      simp [hfh, hsq]
  · rw [h5s, Store.read_of_write_eq_some_of_ne w5 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne w4 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne w3 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne w2 (Or.inl hb),
      Store.read_of_write_eq_some_of_ne w1 (Or.inl hb)]

omit [Inhabited K] in
/-- The sizes, the root's matrix and its window: from a state whose buffers `c + 5` (sizes, of
$n(\ell_0 + 2) + 1$ cells), `c + 1` (node matrices) and `c + 8` (windows) have the shapes that
`NLAlib.eighProg` allocates, whose block at offset $0$ of `A` holds $\mathbf{A}$ and whose cells
$0$, $1$ of `par` hold $R_0$, $\varepsilon$, the size loop, the root's size, the copy of
$\mathbf{A}$ and the copies of $R_0$, $\varepsilon$ succeed (exact integer literals up to $n + 4$,
the exact floor conversion), and the rest succeeds when it does from every state at the same tape
positions and shape that reads as the start outside these three buffers, whose sizes read $n$ at
slot $0$ and $0$ elsewhere, whose root block of `c + 1` holds $\mathbf{A}$ and whose cells $0$, $1$
of `c + 8` hold $R_0$, $\varepsilon$. -/
private theorem exists_exec_root {dec : P → K → ℝ} (p : P) (n ℓ₀ : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) {A par c : ℕ}
    {σ : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε : K} (hA1 : c + 1 ≠ A)
    (hA5 : A ≠ c + 5) (hp1 : par ≠ c + 1) (hp5 : par ≠ c + 5) (hp8 : par ≠ c + 8)
    (hsMa : σ.store.shape[c + 1]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)))
    (hsSz : σ.store.shape[c + 5]? = some (p, n * (ℓ₀ + 1 + 1) + 1))
    (hsLv : σ.store.shape[c + 8]? = some (p, 2 * (ℓ₀ + 1 + 1)))
    (hA : pairLayout.Holds σ.store p A 0 A₀)
    (hR : σ.store.read p par 0 = some R₀) (hε : σ.store.read p par 1 = some ε)
    {t : Builder P ι ℕ ℕ Unit}
    (ht : ∀ σ' : St P K C, σ'.store.shape = σ.store.shape → σ'.pos = σ.pos →
      (∀ q b i, b ≠ c + 1 → b ≠ c + 5 → b ≠ c + 8 → σ'.store.read q b i = σ.store.read q b i) →
      pairLayout.Holds σ'.store p (c + 1) 0 A₀ → ReadsIdx I.sem σ'.store p (c + 5) 0 n →
      (∀ j, j ≠ 0 → j < n * (ℓ₀ + 1 + 1) + 1 → ReadsIdx I.sem σ'.store p (c + 5) j 0) →
      σ'.store.read p (c + 8) 0 = some R₀ → σ'.store.read p (c + 8) 1 = some ε →
      ∃ st', exec I t.run σ' = some st') :
    ∃ st', exec I (Builder.run (ι := ι) (do
      forRange (IExp.const n * (IExp.const ℓ₀ + 1 + 1) + 1) fun w =>
        ins (.litIdx p ⟨c + 5, .var w⟩ 0)
      ins (.litIdx p ⟨c + 5, 0⟩ (.const n))
      zcopy p (.const n) (.const n) A 0 (c + 1) 0
      ins (.copy p ⟨c + 8, 0⟩ ⟨par, 0⟩)
      ins (.copy p ⟨c + 8, 1⟩ ⟨par, 1⟩)
      t)) σ = some st' := by
  obtain ⟨z0, hz0, -⟩ := hlit p 0 (by omega)
  obtain ⟨zn, hzn, -⟩ := hlit p n (by omega)
  -- the sizes
  obtain ⟨σ6, h6, sh6, p6, r6, fr6⟩ := exists_exec_loop_litIdx (ι := ι) (st := σ)
    (m := IExp.const n * (IExp.const ℓ₀ + 1 + 1) + 1) (by exact hz0) hsSz le_rfl
  refine exists_exec_bind_of_exec (by exact (exec_seq_skip I _ _).trans h6) ?_ (by intro _; rfl)
  obtain ⟨S7, w7⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) zn
    (by rw [sh6]; exact hsSz) (by positivity)
  refine exists_exec_seq_litIdx (by exact hzn) (by exact w7) ?_
  refine exists_exec_of_forall_eq fun σ7 hσ7 => ?_
  have h7s : σ7.store = S7 := by rw [hσ7]
  have sh7 : σ7.store.shape = σ.store.shape := by
    rw [h7s, Store.shape_of_write_eq_some w7, sh6]
  have fr7 : ∀ q b i, b ≠ c + 5 → σ7.store.read q b i = σ.store.read q b i :=
    fun q b i h => by rw [h7s, Store.read_of_write_eq_some_of_ne w7 (Or.inl h), fr6 q b i h]
  -- the root's matrix
  have hA7 : pairLayout.Holds σ7.store p A 0 A₀ :=
    hA.of_forall_read_eq fun i _ _ => fr7 _ _ _ hA5
  obtain ⟨σ8, h8⟩ := exists_exec_zcopy (ι := ι) p n n (X := A) (xo := 0) (Y := c + 1) (yo := 0)
    hA7 (blockDisjoint_of_ne hA1) ⟨_, by rw [sh7]; exact hsMa, by
      change 0 + 2 * (n * n) ≤ 2 * (n * n) * (ℓ₀ + 1 + 1)
      nlinarith⟩
  obtain ⟨HMa, F8, S8, P8⟩ := holds_of_exec_zcopy p n n hA7 (blockDisjoint_of_ne hA1) h8
  refine exists_exec_bind_of_exec (by exact h8) ?_ (by intro _; rfl)
  have fr8 : ∀ q b i, b ≠ c + 5 → b ≠ c + 1 → σ8.store.read q b i = σ.store.read q b i :=
    fun q b i h1 h2 => (F8 q b i (blockDisjoint_of_ne h2)).trans (fr7 q b i h1)
  -- the window and tolerance of the root
  obtain ⟨S9, w9⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) R₀
    (by rw [S8, sh7]; exact hsLv) (by omega)
  refine exists_exec_seq_copy (by exact (fr8 p par 0 hp5 hp1).trans hR) (by exact w9) ?_
  obtain ⟨S10, w10⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) ε
    (by rw [Store.shape_of_write_eq_some w9, S8, sh7]; exact hsLv) (by omega)
  have r9 : S9.read p par 1 = some ε :=
    (Store.read_of_write_eq_some_of_ne w9 (Or.inl hp8)).trans ((fr8 p par 1 hp5 hp1).trans hε)
  refine exists_exec_seq_copy (by exact r9) (by exact w10) ?_
  refine exists_exec_of_forall_eq fun σ10 hσ10 => ?_
  have h10s : σ10.store = S10 := by rw [hσ10]
  have fr10 : ∀ q b i, b ≠ c + 8 → σ10.store.read q b i = σ8.store.read q b i :=
    fun q b i h => by
      rw [h10s, Store.read_of_write_eq_some_of_ne w10 (Or.inl h),
        Store.read_of_write_eq_some_of_ne w9 (Or.inl h)]
  have hSz10 : ∀ i, σ10.store.read p (c + 5) i = σ7.store.read p (c + 5) i := fun i =>
    (fr10 p _ i (by omega)).trans (F8 p _ i (blockDisjoint_of_ne (by omega)))
  refine ht σ10 ?_ ?_ (fun q b i h1 h5 h8 => (fr10 q b i h8).trans (fr8 q b i h5 h1))
    (HMa.of_forall_read_eq fun i _ _ => fr10 p _ i (by omega)) ?_ (fun j hj0 hj => ?_) ?_ ?_
  · rw [h10s, Store.shape_of_write_eq_some w10, Store.shape_of_write_eq_some w9, S8, sh7]
  · rw [hσ10]; exact P8.trans (by rw [hσ7]; exact p6)
  · refine readsIdx_of_read_eq_lit hlit htn (k := n) (by omega) ?_
    rw [hSz10, h7s, Store.read_of_write_eq_some w7]; exact hzn.symm
  · refine readsIdx_of_read_eq_lit hlit htn (k := 0) (by omega) ?_
    rw [hSz10, h7s, Store.read_of_write_eq_some_of_ne w7 (Or.inr hj0), r6 j hj]
    exact hz0.symm
  · rw [h10s, Store.read_of_write_eq_some_of_ne w10 (Or.inr (by omega))]
    exact Store.read_of_write_eq_some w9
  · rw [h10s]; exact Store.read_of_write_eq_some w10

/-- After the allocations, the run of `NLAlib.eighProg` succeeds: the initialisation writes
the constants, the sizes ($n$ at slot $0$ and $0$ elsewhere), $\mathbf{A}$, $R_0$ and
$\varepsilon$ at depth $0$, which are the hypotheses of `exists_exec_eighPasses`. -/
private theorem exists_exec_eighProgBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (hℓ : 1 ≤ ℓ₀)
    {A par U dv c Ma Ua Qa Ea Sz Kd Kp Lv Su Sg : ℕ} {σ : St P K C}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hMa : Ma = c + 1) (hUa : Ua = c + 2) (hQa : Qa = c + 3) (hEa : Ea = c + 4) (hSz : Sz = c + 5)
    (hKd : Kd = c + 6) (hKp : Kp = c + 7) (hLv : Lv = c + 8) (hSu : Su = c + 9)
    (hSg : Sg = c + 10) (hlt : ∀ j ∈ [A, par, U, dv], j < c)
    (hsc : σ.store.shape[c]? = some (p, 5))
    (hsMa : σ.store.shape[Ma]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)))
    (hsUa : σ.store.shape[Ua]? = some (p, 2 * (n * n) * (ℓ₀ + 1 + 1)))
    (hsQa : σ.store.shape[Qa]? = some (p, 2 * (n * n) * (ℓ₀ + 1)))
    (hsEa : σ.store.shape[Ea]? = some (p, n * (ℓ₀ + 1 + 1)))
    (hsSz : σ.store.shape[Sz]? = some (p, n * (ℓ₀ + 1 + 1) + 1))
    (hsKd : σ.store.shape[Kd]? = some (p, n * (ℓ₀ + 1)))
    (hsKp : σ.store.shape[Kp]? = some (p, n * (ℓ₀ + 1)))
    (hsLv : σ.store.shape[Lv]? = some (p, 2 * (ℓ₀ + 1 + 1)))
    (hsSu : σ.store.shape[Su]? = some (p, n)) (hsSg : σ.store.shape[Sg]? = some (p, 4 * (n * n)))
    (hA : pairLayout.Holds σ.store p A 0 A₀)
    (hpar : σ.store.read p par 0 = some R₀ ∧ σ.store.read p par 1 = some ε ∧
      σ.store.read p par 2 = some β)
    (hU : ∃ len, σ.store.shape[U]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hdv : ∃ len, σ.store.shape[dv]? = some (p, len) ∧ n ≤ len)
    (hpos : σ.pos .uniform = 0 ∧ σ.pos .gaussian = 0) :
    ∃ st', exec I (Builder.run (ι := ι) (do
      ins (.lit p ⟨c, 0⟩ 1)
      ins (.litIdx p ⟨c, 1⟩ 2)
      ins (.bin p .div ⟨c, 2⟩ ⟨c, 0⟩ ⟨c, 1⟩)
      ins (.un p .neg ⟨c, 3⟩ ⟨c, 0⟩)
      ins (.un p .sqrt ⟨c, 4⟩ ⟨c, 2⟩)
      forRange (IExp.const n * (IExp.const ℓ₀ + 1 + 1) + 1) fun w =>
        ins (.litIdx p ⟨Sz, .var w⟩ 0)
      ins (.litIdx p ⟨Sz, 0⟩ (.const n))
      zcopy p (.const n) (.const n) A 0 Ma 0
      ins (.copy p ⟨Lv, 0⟩ ⟨par, 0⟩)
      ins (.copy p ⟨Lv, 1⟩ ⟨par, 1⟩)
      forRange (IExp.const ℓ₀ + 1) fun d =>
        eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv Su Sg Ma Ua Qa Ea
          Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
      eighBottomLevel p (.const n) (IExp.const ℓ₀ + 1) Ua Ea Sz
      forRange (IExp.const ℓ₀ + 1) fun d' =>
        eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩
      zcopy p (.const n) (.const n) Ua 0 U 0
      forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨Ea, .var i⟩))) σ = some st' := by
  subst hMa hUa hQa hEa hSz hKd hKp hLv hSu hSg
  have lA : A < c := hlt A (by simp)
  have lpar : par < c := hlt par (by simp)
  have lU : U < c := hlt U (by simp)
  have ldv : dv < c := hlt dv (by simp)
  refine exists_exec_consts (mmR := mmR) (qrR := qrR) hsem p hu hlit (by omega) hsc
    fun σ5 hc5 sh5 fr5 p5 => ?_
  refine exists_exec_root p n ℓ₀ hlit htn (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [sh5]; exact hsMa) (by rw [sh5]; exact hsSz) (by rw [sh5]; exact hsLv)
    (hA.of_forall_read_eq fun i _ _ => fr5 _ _ _ (by omega)) ((fr5 _ _ _ (by omega)).trans hpar.1)
    ((fr5 _ _ _ (by omega)).trans hpar.2.1)
    fun σ10 sh10 p10 fr10 HMa hSz0 hSzj hLv0 hLv1 => ?_
  have sh10' : σ10.store.shape = σ.store.shape := sh10.trans sh5
  have frσ : ∀ q b i, b ≠ c → b ≠ c + 1 → b ≠ c + 5 → b ≠ c + 8 →
      σ10.store.read q b i = σ.store.read q b i :=
    fun q b i h0 h1 h5 h8 => (fr10 q b i h1 h5 h8).trans (fr5 q b i h0)
  let H : EighArenas := ⟨c + 1, c + 2, c + 3, c + 4, c + 5, c + 6, c + 7, c + 8⟩
  refine exists_exec_eighPasses hmm hqr hsem p hu n ℓ₀ F hlit htn hℓ H (par := par) (Su := c + 9)
      (Sg := c + 10)
    (c := c) (U := U) (dv := dv) (A₀ := A₀) (σ := σ10) (R₀ := R₀) (ε := ε) (β := β) hε hR₀
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨by simp [H, EighArenas.handles], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [sh10'] <;> assumption
  · simp [H, EighArenas.handles]; omega
  · simp [H, EighArenas.handles]; omega
  · simp [H, EighArenas.handles]; omega
  · -- the root at depth 0
    refine ⟨fun a lo y ha hay => ?_, fun lo hlo hno => ?_, hLv0, hLv1⟩
    · rw [List.length_eq_zero_iff.mp ha] at hay
      cases hay
      exact ⟨by simpa only [Nat.mul_zero, Nat.add_zero] using hSz0,
        by simpa only [Nat.mul_zero, Nat.add_zero] using HMa⟩
    · have hlo0 : lo ≠ 0 := by
        rintro rfl
        exact hno [] _ rfl rfl
      simpa only [Nat.mul_zero, Nat.zero_add] using hSzj lo hlo0 (by nlinarith)
  · intro j hj1 hj2
    by_cases hj0 : j = 0
    · subst hj0
      rwa [show n = 0 by omega] at hSz0
    · exact hSzj j hj0 (by omega)
  · rw [p10, p5]; exact hpos
  · exact ⟨(frσ p par 0 (by omega) (by omega) (by omega) (by omega)).trans hpar.1,
      (frσ p par 2 (by omega) (by omega) (by omega) (by omega)).trans hpar.2.2⟩
  · exact ⟨n, by rw [sh10']; exact hsSu, le_rfl⟩
  · exact ⟨4 * (n * n), by rw [sh10']; exact hsSg, le_rfl⟩
  · exact EighConsts.of_read_eq (fun i => fr10 p c i (by omega) (by omega) (by omega)) hc5
  · rw [sh10']; exact hU
  · rw [sh10']; exact hdv

omit [DecidableEq P] [Inhabited K] in
/-- The shape of a pushed store below or above its top. -/
private theorem getElem?_shape_push_of_ne {s : Store P K} {b : ℕ} (x : P × Array (Option K))
    (hb : b ≠ s.size) :
    (Store.shape (s.push x))[b]? = s.shape[b]? := by
  simp [Store.shape, Array.getElem?_push, hb]

/-- The refinement of the spectral bisection program, success: under the standard model at $u$
with every value in range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor
conversion, if the kernels `mm`, `qr` of `I` are routines on interleaved pairs, $\ell_0 \ge 1$,
$\varepsilon$ and $R_0$ decode to nonnegative values, and the buffers `U`, `dv` at tag `p` have
$2n^2$ and $n$ cells, then every run of `NLAlib.eighProg` succeeds from a state with the tape
positions at $0$, whose distinct buffers `A`, `par`, `U`, `dv` exist, whose block at offset $0$ of
`A` holds the stored $\mathbf{A}$ and whose cells $0$, $1$, $2$ of `par` hold $R_0$,
$\varepsilon$, $\beta$. No printed source. -/
theorem exists_exec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (hℓ : 1 ≤ ℓ₀) {A par U dv : ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hbufs : [A, par, U, dv].Nodup) (hsize : ∀ j ∈ [A, par, U, dv], j < st.store.size)
    (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0)
    (hU : ∃ len, st.store.shape[U]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hdv : ∃ len, st.store.shape[dv]? = some (p, len) ∧ n ≤ len) :
    ∃ st', exec I (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run st =
      some st' := by
  have _ := hbufs
  have lA := hsize A (by simp)
  have lpar := hsize par (by simp)
  have lU := hsize U (by simp)
  have ldv := hsize dv (by simp)
  change ∃ st', exec I (.seq (.alloc p 5 _) .skip) st = some st'
  rw [exec_seq_skip]
  refine exists_exec_alloc_of_exists ?_
  iterate 10
    change ∃ a, exec I (.alloc p _ _) _ = some a
    refine exists_exec_alloc_of_exists ?_
  refine exists_exec_eighProgBody hmm hqr hsem p hu n ℓ₀ F hlit htn hℓ (A := A) (par := par)
      (U := U) (dv := dv)
    (A₀ := A₀) (R₀ := R₀) (ε := ε) (β := β) hε hR₀ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsize
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | (simp only [Array.size_push]; done)
    | (simp (disch := ((try simp only [Array.size_push]); omega)) only [getElem?_shape_push_of_ne,
        Store.getElem?_shape_push_size]; done)
    | (simp (disch := ((try simp only [Array.size_push]); omega)) only [getElem?_shape_push_of_ne,
        Store.getElem?_shape_push_size]; rfl)
    | skip
  · exact hA.of_forall_read_eq fun i _ _ => by
      simp (disch := ((try simp only [Array.size_push]); omega)) only [Store.read_push_of_ne]
  · simp (disch := ((try simp only [Array.size_push]); omega)) only [Store.read_push_of_ne]
    exact hpar
  · simp (disch := ((try simp only [Array.size_push]); omega)) only [getElem?_shape_push_of_ne]
    exact hU
  · simp (disch := ((try simp only [Array.size_push]); omega)) only [getElem?_shape_push_of_ne]
    exact hdv
  · exact hpos

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The registered tree instantiates to the builder: at the sizes $N$ and $(\ell_0, F)$ the tree
`NLAlib.eighProg.compiled` is `NLAlib.eighProg` on the declared buffers $0$ to $3$. No printed
source. -/
theorem eighProg.toStmt_compiled (p : P) (mm qr : ι) (N : ℕ) (n : Fin 2 → ℕ) :
    (eighProg.compiled p mm qr).toStmt N n =
      ProgFamily.inst (r := 2) (b := 4) (fun _ _ N n h =>
        (eighProg p mm qr N (n 0) (n 1) (h 0) (h 1) (h 2) (h 3)).run) N n := by
  -- the unfolding of the four buffers is deeper than the default recursion limit
  set_option maxRecDepth 10000 in rfl

/-- The registered tree computes `NLAlib.eigh`: let the kernels `mm`, `qr` of `I` be the routines
`mmR`, `qrR` on interleaved pairs, and the semantics decide flags at `p`, with exact integer
literals up to $N + 4$ and the exact floor conversion. A successful run of
`NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$ from the initial state with the
stored $\mathbf{A}$, the stored $R_0$, $\varepsilon$, $\beta$, and $2N^2$ and $N$ empty cells as
declared buffers ends with declared buffers $2$ and $3$ holding `NLAlib.eigh` on the machine of
the interpretation with the tree of samples at the slots.
No printed source. -/
theorem eighProg.holds_of_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (N ℓ₀ F : ℕ) (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (R₀ ε β : K) {st' : St P K C}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some R₀, some ε, some β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none]) = some st') :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M N F R₀ β 0 0 ⟨N, A₀, R₀, ε, ℓ₀⟩)
    pairLayout.Holds st'.store p 2 0 r.1 ∧ ∀ i : Fin N, st'.store.read p 3 i = some (r.2 i) := by
  rw [Prog.exec_eq_exec_toStmt, eighProg.toStmt_compiled] at h
  set bufs : List (Array (Option K)) := [(pairLayout.toArray A₀).map some,
    #[some R₀, some ε, some β], Array.replicate (2 * (N * N)) none, Array.replicate N none]
    with hbufs
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (bufs := bufs) (k := 0) (Y := A₀)
    rfl
  have h' : exec I (eighProg p mm qr (.const N) (.const ℓ₀) (.const F) 0 1 2 3).run
      (inputState p bufs) = some st' := h
  exact holds_of_exec_eighProg hmm hqr p hflag hcmp N ℓ₀ F hlit htn (by simp)
    (by simp [inputState, bufs]) hA (by simp [inputState, bufs, Store.read])
    (by simp [inputState]) h'

/-- The registered tree succeeds: under the standard model at $u$ with every value in range,
$u(p) < 1$, exact integer literals up to $N + 4$ and the exact floor conversion, if the kernels
`mm`, `qr` of `I` are routines on interleaved pairs, $\ell_0 \ge 1$ and $\varepsilon$, $R_0$
decode to nonnegative values, then every run of `NLAlib.eighProg.compiled` at the sizes $N$ and
$(\ell_0, F)$ from the initial state with the stored $\mathbf{A}$, the stored $R_0$,
$\varepsilon$, $\beta$, and $2N^2$ and $N$ empty cells as declared buffers succeeds. No printed
source. -/
theorem eighProg.exists_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (N ℓ₀ F : ℕ)
    (hℓ : 1 ≤ ℓ₀) (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (R₀ ε β : K) (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀) :
    ∃ st' : St P K C, (eighProg.compiled p mm qr).exec I N ![ℓ₀, F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some R₀, some ε, some β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none]) = some st' := by
  rw [Prog.exec_eq_exec_toStmt, eighProg.toStmt_compiled]
  set bufs : List (Array (Option K)) := [(pairLayout.toArray A₀).map some,
    #[some R₀, some ε, some β], Array.replicate (2 * (N * N)) none, Array.replicate N none]
    with hbufs
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (bufs := bufs) (k := 0) (Y := A₀)
    rfl
  exact exists_exec_eighProg hmm hqr hsem p hu N ℓ₀ F hlit htn hℓ (A := 0) (par := 1) (U := 2)
    (dv := 3) (st := inputState p bufs) (A₀ := A₀) (R₀ := R₀) (ε := ε) (β := β) hε hR₀
    (by simp) (by simp [inputState, bufs]) hA (by simp [inputState, bufs, Store.read])
    (by simp [inputState]) ⟨2 * (N * N), by simp [inputState, Store.getElem?_shape, bufs], by simp⟩
    ⟨N, by simp [inputState, Store.getElem?_shape, bufs], by simp⟩

end NLAlib
