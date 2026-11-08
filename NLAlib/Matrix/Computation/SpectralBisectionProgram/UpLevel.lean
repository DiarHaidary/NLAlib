/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.UpSlot

/-!
# The upward level of the spectral bisection program

One level of the upward pass of `NLAlib.eighProg` (`NLAlib.eighUpLevel`) takes the outputs of depth
$d + 1$ to those of depth $d$ (`NLAlib.EighArenas.OutHolds`), slot by slot
(`NLAlib.holds_of_exec_eighUpSlot`).

## Main results

* `NLAlib.holds_of_exec_eighUpLevel`: what a successful level computes.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

omit [AddMonoid C] [Inhabited K] in
/-- The level encoding of the arenas `H` reads only the arenas: it transfers to a store `s'`
that reads as `s` there. -/
theorem EighArenas.holds_of_forall_read_eq {H : EighArenas} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ D d : ℕ} {R₀ β : K} {root : EighNode K}
    {sem : ScalarSem P K} (hs : ∀ q b i, b ∈ H.handles → s'.read q b i = s.read q b i) :
    (H.LevelHolds sem s p M n F ℓ₀ R₀ β root d → H.LevelHolds sem s' p M n F ℓ₀ R₀ β root d) ∧
      (H.RecordHolds sem s p M n F R₀ β root d → H.RecordHolds sem s' p M n F R₀ β root d) ∧
      (H.OutHolds s p M n F D R₀ β root d → H.OutHolds s' p M n F D R₀ β root d) := by
  have hm : ∀ {b}, b ∈ [H.Ma, H.Ua, H.Qa, H.Ea, H.Sz, H.Kd, H.Kp, H.Lv] → b ∈ H.handles :=
    fun h => h
  have hR : ∀ {b i k}, b ∈ H.handles → ReadsIdx sem s p b i k → ReadsIdx sem s' p b i k :=
    fun hb h => readsIdx_of_read_eq (hs p _ _ hb) h
  have hH : ∀ {b off l m} {Y : Matrix (Fin l) (Fin m) (K × K)}, b ∈ H.handles →
      pairLayout.Holds s p b off Y → pairLayout.Holds s' p b off Y :=
    fun hb h => h.of_forall_read_eq fun i _ _ => hs p _ i hb
  refine ⟨fun h => ⟨fun a lo y ha hay => ?_, fun lo hlo hno => ?_, ?_, ?_⟩,
    fun h a lo y ha hay hk => ?_, fun h a lo y ha hay => ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 a lo y ha hay
    exact ⟨hR (hm (by simp)) h1, hH (hm (by simp)) h2⟩
  · exact hR (hm (by simp)) (h.2.1 lo hlo hno)
  · rw [hs p _ _ (hm (by simp))]; exact h.2.2.1
  · rw [hs p _ _ (hm (by simp))]; exact h.2.2.2
  · have := h a lo y ha hay hk
    split at this
    · obtain ⟨h1, h2, h3⟩ := this
      exact ⟨hR (hm (by simp)) h1, hH (hm (by simp)) h2,
        fun i => (hs p _ _ (hm (by simp))).trans (h3 i)⟩
    · exact hR (hm (by simp)) this
    · obtain ⟨h1, h2, h3, h4⟩ := this
      exact ⟨hR (hm (by simp)) h1, hR (hm (by simp)) h2, hH (hm (by simp)) h3,
        hH (hm (by simp)) h4⟩
  · obtain ⟨h1, h2⟩ := h a lo y ha hay
    exact ⟨hH (hm (by simp)) h1, fun i => (hs p _ _ (hm (by simp))).trans (h2 i)⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The handles of arenas `H` allocated in the store `s` are below its size. -/
theorem EighArenas.Shaped.lt_size_of_mem {H : EighArenas} {s : Store P K} {p : P} {n D b : ℕ}
    (hH : H.Shaped s p n D) (hb : b ∈ H.handles) : b < s.size := by
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, s.shape[b]? = some x → b < s.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := hH
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv]

omit [AddMonoid C] in
/-- The shift cells of a level: once $\mathrm{fl}(x / \mathrm{fl}(2))$ is written at cell $0$ of
buffer `t` and its negation at cell $1$, they hold $\sigma$ and $-\sigma$ as the machine of the
interpretation computes them. -/
theorem read_eq_div_and_read_eq_neg_of_write {p : P} {st wa wb : Store P K} {t : ℕ}
    {x z2 v0 v1 : K} (hz2 : I.sem.lit p ((2 : ℕ) : ℚ) = some z2)
    (hv0 : I.sem.bin p .div x z2 = some v0) (hv1 : I.sem.un p .neg v0 = some v1)
    (hwa : st.write p t 0 v0 = some wa) (hwb : wa.write p t 1 v1 = some wb) :
    wb.read p t 0 = some ((eighTapeMachine I p mmR qrR).div x
        ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      wb.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
        ((eighTapeMachine I p mmR qrR).div x ((eighTapeMachine I p mmR qrR).ofNat 2))) := by
  refine ⟨?_, ?_⟩
  · rw [Store.read_of_write_eq_some_of_ne hwb (Or.inr (by decide)),
      Store.read_of_write_eq_some hwa]
    change some v0 = some ((I.sem.bin p .div x ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD
      default)
    rw [hz2, Option.getD_some, hv0, Option.getD_some]
  · rw [Store.read_of_write_eq_some hwb]
    change some v1 = some ((I.sem.un p .neg ((I.sem.bin p .div x
      ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)).getD default)
    rw [hz2, Option.getD_some, hv0, Option.getD_some, hv1, Option.getD_some]

omit [AddMonoid C] [Inhabited K] in
/-- Freeing the scratch buffer (handle `st.size`, pushed onto `st` and written into `wb`) after the
slots of a level: the outputs of depth $d$ written into `s`, and every cell of `st` outside them,
are kept. -/
private theorem holds_pop_of_holds {H : EighArenas} {st wb s : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F D d ℓ₀ : ℕ} {R₀ β ε : K} {A : Matrix (Fin n) (Fin n) (K × K)}
    {x : P × Array (Option K)} (hltH : ∀ b ∈ H.handles, b < st.size)
    (hwsh : wb.shape = Store.shape (st.push x))
    (hrd₀ : ∀ q b i, b < st.size → wb.read q b i = st.read q b i) (hsh : s.shape = wb.shape)
    (hfr : ∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) → s.read q b i = wb.read q b i)
    (hdone : ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) → lo' < n →
      pairLayout.Holds s p H.Ua (2 * (n * n) * d + 2 * n * lo')
          (eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).1 ∧
        ∀ i : Fin y.k, s.read p H.Ea (n * d + lo' + i) = some
          ((eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).2 i)) :
    H.OutHolds s.pop p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) →
        Store.read s.pop q b i = st.read q b i) ∧
      Store.shape s.pop = st.shape := by
  have hs₁ : s.size = st.size + 1 := by
    have := congrArg Array.size hsh
    rw [hwsh] at this
    simpa [Store.shape] using this
  have hpop : ∀ {q : P} {b i : ℕ}, b < st.size → Store.read s.pop q b i = s.read q b i :=
    fun hb => Store.read_pop_of_lt (by omega)
  refine ⟨fun a lo y ha hay => ?_, fun q b i hb => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hy0 : y.k = 0 := by
        cases a with
        | nil => cases hay; rfl
        | cons b a => simp [eighLoc, eighStep] at hay
      have hk : ∀ i : Fin y.k, False := fun i => absurd i.isLt (by omega)
      exact ⟨fun i => (hk i).elim, fun i => (hk i).elim⟩
    have hb := eighLoc_bounds hn hay
    obtain ⟨hU, hE⟩ := hdone a lo y ha hay (by omega)
    exact ⟨hU.of_forall_read_eq fun i _ _ => hpop (hltH _ (by simp [EighArenas.handles])),
      fun i => (hpop (hltH _ (by simp [EighArenas.handles]))).trans (hE i)⟩
  · by_cases hbt : b < st.size
    · exact (hpop hbt).trans ((hfr q b i hb).trans (hrd₀ q b i hbt))
    · have hsz' : (Array.pop s).size = st.size := by simp [hs₁]
      exact (Store.read_eq_none_of_size_le (by omega)).trans
        (Store.read_eq_none_of_size_le (by omega)).symm
  · rw [Store.shape_pop, hsh, hwsh]
    simp [Store.shape]

/-- One level of the upward pass: if kernel `mm` of `I` is the routine `mmR` on interleaved pairs,
under exact integer literals up to $n + 4$, a successful run of `NLAlib.eighUpLevel` at depth
$d < D$ from a state whose arenas hold the nodes of depth $d$ (their sizes), the records of depth
$d$ and the outputs of depth $d + 1$, with the window of depth $d$ in its cell and the stored
$\mathrm{fl}(2)$ in `two`, ends with the outputs of depth $d$ (`NLAlib.EighArenas.OutHolds` at $d$,
budget $D - d$); every cell outside the output and eigenvalue arenas at depth $d$ is unchanged, the
store shape and the tape positions too. No printed source. -/
theorem holds_of_exec_eighUpLevel {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {dec : P → K → ℝ} (p : P) (n ℓ₀ F d D : ℕ) (hd : d < D)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (H : EighArenas)
    {two : Cell ℕ ℕ} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D)
    (htwov : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (h : exec I (eighUpLevel p mm (.const n) (.const d) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
      two).run st = some st') :
    H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hnd := hH.1
  have hltH : ∀ b ∈ H.handles, b < st.store.size := fun b hb => hH.lt_size_of_mem hb
  have htH : st.store.size ∉ H.handles := fun hm => absurd (hltH _ hm) (lt_irrefl _)
  obtain ⟨z2, hz2, -⟩ := hlit p 2 (by omega)
  have htwo' : st.store.read p two.buf two.idx.eval = some z2 := htwov.trans hz2
  have ltwo := Store.lt_size_of_read_eq_some htwo'
  set M := eighTapeMachine I p mmR qrR with hM
  -- the scope and the scratch cells
  change exec I (.seq (.alloc p _ _) .skip) st = some st' at h
  rw [exec_seq_skip, exec_alloc] at h
  obtain ⟨s₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
  change exec I (.seq (.instr _) (.seq (.instr _) (.seq (.loop _ _) .skip))) _ = some s₁ at h₁
  rw [exec_seq] at h₁
  obtain ⟨σa, ha, h₁⟩ := Option.bind_eq_some_iff.mp h₁
  rw [exec_seq] at h₁
  obtain ⟨σb, hb, h₁⟩ := Option.bind_eq_some_iff.mp h₁
  rw [exec_seq_skip] at h₁
  rw [exec_instr] at ha hb
  obtain ⟨ra, hra, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨rb, hrb, rfl⟩ := Option.map_eq_some_iff.mp hb
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hra hrb
  obtain ⟨xR, hxR, x2, hx2, v0, hv0, wa, hwa, rfl⟩ := hra
  obtain ⟨x0, hx0, v1, hv1, wb, hwb, rfl⟩ := hrb
  set t := st.store.size with ht
  have hP : ∀ {q : P} {b i : ℕ}, b < t →
      Store.read (st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)) q b i =
        st.store.read q b i := fun hb => Store.read_push_of_lt hb
  have hrd₀ : ∀ q b i, b < t → wb.read q b i = st.store.read q b i := fun q b i hb => by
    rw [Store.read_of_write_eq_some_of_ne hwb (Or.inl (Nat.ne_of_lt hb)),
      Store.read_of_write_eq_some_of_ne hwa (Or.inl (Nat.ne_of_lt hb)), hP hb]
  rw [hP (hltH _ (by simp [EighArenas.handles]))] at hxR
  rw [show (2 * IExp.const d : IExp ℕ).eval = 2 * d from rfl, hlev.2.2.1] at hxR
  cases hxR
  rw [hP ltwo, htwo'] at hx2
  cases hx2
  rw [Store.read_of_write_eq_some hwa] at hx0
  cases hx0
  have hv0' : I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1 z2 = some v0 := hv0
  rw [IExp.eval_zero] at hwa
  rw [IExp.eval_one] at hwb
  dsimp only at hwb ⊢
  obtain ⟨ht0, ht1⟩ := read_eq_div_and_read_eq_neg_of_write (mmR := mmR) (qrR := qrR) hz2 hv0'
    hv1 hwa hwb
  have hT := fun d' => EighArenas.holds_of_forall_read_eq (H := H) (p := p) (M := M) (n := n)
    (F := F) (ℓ₀ := ℓ₀) (D := D) (d := d') (R₀ := R₀) (β := β) (root := ⟨n, A, R₀, ε, ℓ₀⟩)
    (sem := I.sem) fun q b i hb => hrd₀ q b i (hltH b hb)
  refine (fun L => ?_) (forall_of_exec_loop_eq_some I (n := .const n)
    (fun lo (s : St P K C) =>
      H.UpSlotsDone s { st with store := wb } p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d lo)
    ?_ ?_ h₁)
  rotate_left
  · exact ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · exact fun lo hlo s₂ s₃ ⟨hsh, hps, hfr, hdone⟩ hex =>
      holds_of_exec_eighUpSlot hmm p n ℓ₀ F d D hd H t (s₀ := { st with store := wb })
        (by simpa using hlo) hnd htH ht0 ht1
        ((hT d).1 hlev) ((hT d).2.1 hrec) ((hT (d + 1)).2.2 hout) ⟨hsh, hps, hfr, hdone⟩ hex
  obtain ⟨Lsh, Lps, Lfr, Ldone⟩ := L
  simp only [IExp.eval_const] at Ldone
  obtain ⟨O1, O2, O3⟩ := holds_pop_of_holds (ℓ₀ := ℓ₀) (D := D) (M := M) hltH
    (by rw [Store.shape_of_write_eq_some hwb, Store.shape_of_write_eq_some hwa]) hrd₀ Lsh
    (fun q b i hb => Lfr q b i (Or.inl hb)) Ldone
  exact ⟨O1, O2, O3, Lps⟩

end NLAlib
