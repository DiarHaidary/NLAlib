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
(`NLAlib.spec_eighUpSlot`), as a routine specification in both modes.

## Main results

* `NLAlib.spec_eighUpLevel`: the level as a routine specification.
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


/-- The two scalar instructions at the head of `NLAlib.eighUpLevel`, in the
weakest-precondition form: in the allocated scratch buffer `b` they write $\sigma =
\mathrm{fl}(R / z_2)$ and $-\sigma$ (the stored window $R$ at the cell $2d$ of `Lv`, the stored
$z_2$ in the cell `two`), then the rest `X` runs from there. No printed source. -/
theorem wp_eighUpHead (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (d b Lv : ℕ)
    {two : Cell ℕ ℕ} {st : St P K C} {R z2 : K} (hsz : st.store.size = b) (hLv : Lv < b)
    (hR : st.store.read p Lv (2 * d) = some R)
    (hz : st.store.read p two.buf two.idx.eval = some z2) (hdz : dec p z2 ≠ 0)
    (X : Builder P ι ℕ ℕ Unit) {Q : St P K C → Prop}
    (hX : ∀ st₂ : St P K C,
      Modifies [(b, 0, 1), (b, 1, 1)] (st.allocate p (2 : IExp ℕ).eval (I.width p)).store
        st₂.store →
      PosKept (st.allocate p (2 : IExp ℕ).eval (I.width p)) st₂ →
      st₂.store.read p b 0 = some ((I.sem.bin p .div R z2).getD default) →
      st₂.store.read p b 1 = some ((I.sem.un p .neg ((I.sem.bin p .div R z2).getD default)).getD
        default) → Wp md I X.run Q st₂) :
    Wp md I ((ins (.bin p .div ⟨b, 0⟩ ⟨Lv, 2 * IExp.const d⟩ two) : Builder P ι ℕ ℕ Unit) >>=
      fun _ => (ins (.un p .neg ⟨b, 1⟩ ⟨b, 0⟩) >>= fun _ => X)).run Q
      (st.allocate p (2 : IExp ℕ).eval (I.width p)) := by
  have hw := St.writable_allocate st p (2 : IExp ℕ).eval (I.width p)
  rw [hsz] at hw
  have htwo := Store.lt_size_of_read_eq_some hz
  have hR' : (st.allocate p (2 : IExp ℕ).eval (I.width p)).store.read p Lv (2 * d) = some R :=
    (St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega)).trans hR
  have hz' : (st.allocate p (2 : IExp ℕ).eval (I.width p)).store.read p two.buf two.idx.eval =
      some z2 := (St.read_allocate_of_lt _ _ _ _ _ _ _ htwo).trans hz
  refine (RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (dst := ⟨b, 0⟩)
    (x := ⟨Lv, 2 * IExp.const d⟩) (y := two) (op := .div) (a := R) (b := z2))).wp_bind
    ⟨hR', hz', hsem.mono fun hs => ⟨hs.bin_ok p .div R z2 trivial (fun _ => hdz) trivial,
      hw.of_le le_rfl (by simp)⟩⟩ fun st₁ hm₁ h₁ => ?_
  refine (RoutineSpec.ins (spec_un_getD (m := md) (I := I) (p := p) (dst := ⟨b, 1⟩)
    (x := ⟨b, 0⟩) (op := .neg) (a := (I.sem.bin p .div R z2).getD default))).wp_bind
    ⟨h₁.1, hsem.mono fun hs => ⟨(hs.neg p _).imp fun z hz => hz.1,
      (hw.of_modifies hm₁).of_le (by simp) (by simp)⟩⟩ fun st₂ hm₂ h₂ => ?_
  refine hX st₂ (hm₁.trans hm₂)
    (h₂.2.trans h₁.2) ?_ h₂.1
  have := hm₂.2 p b 0 (by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [blockDisjoint])
  change st₂.store.read p b 0 = _
  rw [this]
  exact h₁.1

omit [AddMonoid C] in
/-- Releasing the scratch buffer after the slots of a level: the outputs of depth $d$ written by
the slots (`NLAlib.EighArenas.UpSlotsDone` at $n$) stay stored, as `NLAlib.EighArenas.OutHolds`,
in the released store. No printed source. -/
theorem outHolds_release_of_upSlotsDone {p : P} {n ℓ₀ F d D : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} {H : EighArenas} {s s₀ : St P K C} {len w : ℕ}
    (hdone : H.UpSlotsDone s s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d n)
    (hlt : ∀ x ∈ H.handles, x + 1 < s.store.size) :
    H.OutHolds (s.release p len w).store p (eighTapeMachine I p mmR qrR) n F D R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  intro a lo y ha hay
  have hrd : ∀ b ∈ H.handles, ∀ i, (s.release p len w).store.read p b i = s.store.read p b i :=
    fun b hb i => St.read_release_of_lt s p len w p (hlt b hb) i
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hy0 : y.k = 0 := by
      cases a with
      | nil => cases hay; rfl
      | cons b a => simp [eighLoc, eighStep] at hay
    exact ⟨fun i _ _ => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega)⟩
  · obtain ⟨hU, hE⟩ := hdone.2.2.2 a lo y ha hay (by have := eighLoc_bounds hn hay; omega)
    exact ⟨hU.of_forall_read_eq fun i _ _ => hrd _ (by simp [EighArenas.handles]) i,
      fun i => (hrd _ (by simp [EighArenas.handles]) _).trans (hE i)⟩

/-- One level of the upward pass as a routine specification: if kernel `mm` of `I` is the routine
`mmR` on interleaved pairs, under exact integer literals up to $n + 4$, `NLAlib.eighUpLevel` at
depth $d < D$ from arenas that hold the nodes of depth $d$ (their sizes), the records of depth
$d$ and the outputs of depth $d + 1$, with the stored $\mathrm{fl}(2)$ in the cell `two` and the
scratch buffer on top of the store, leaves the outputs of depth $d$
(`NLAlib.EighArenas.OutHolds` at $d$, budget $D - d$), modifies only the output and eigenvalue
cells of depth $d$ and keeps the tape positions; in mode `total` it also succeeds, given the
standard model with every value in range. No printed source. -/
theorem spec_eighUpLevel {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n ℓ₀ F d D : ℕ)
    (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4)) (H : EighArenas) {two : Cell ℕ ℕ}
    {b : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} :
    RoutineSpec md I (fun st => st.store.size = b ∧ H.Shaped st.store p n D ∧
        st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ) ∧
        H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
        H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
        H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1))
      (eighUpLevel p mm (.const n) (.const d) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp two)
      [(H.Ua, 2 * (n * n) * d, 2 * (n * n)), (H.Ea, n * d, n)]
      fun st st' => H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F D R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ d ∧ PosKept st st' := by
  unfold eighUpLevel
  refine RoutineSpec.scope (Spec.allocBind_named (b := b) (fun st hst => hst.1) ?_)
  rintro s ⟨st, ⟨hsz, hH, htwov, hlev, hrec, hout⟩, rfl⟩
  obtain ⟨z2, hz2, hdz2⟩ := hlit p 2 (by omega)
  have hnd := hH.1
  have hlt : ∀ x ∈ H.handles, x < b := fun x hx => hsz ▸ hH.lt_size_of_mem hx
  have htwo' : st.store.read p two.buf two.idx.eval = some z2 := htwov.trans hz2
  refine wp_eighUpHead md hsem p d b H.Lv hsz (hlt _ (by simp [EighArenas.handles]))
    hlev.2.2.1 htwo' (by rw [hdz2]; norm_num) _ fun st₂ hm₁ hp₁ ht0 ht1 => ?_
  set M := eighTapeMachine I p mmR qrR with hM
  have hM0 : M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2) =
      (I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1 z2).getD default := by
    change (I.sem.bin p .div _ ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default = _
    rw [hz2]; rfl
  have hM1 : M.neg (M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2)) =
      (I.sem.un p .neg ((I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1 z2).getD
        default)).getD default := by rw [hM0]; rfl
  rw [← hM0] at ht0
  rw [← hM1] at ht1
  have hrd : ∀ q b' i, b' ∈ H.handles → st₂.store.read q b' i = st.store.read q b' i :=
    fun q b' i hb' => by
      rw [hm₁.2 q b' i (fun x hx => ?_), St.read_allocate_of_lt _ _ _ _ _ _ _ (by
        have := hlt b' hb'; omega)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact blockDisjoint_of_fst_ne (Nat.ne_of_lt (hlt b' hb'))
  have hT := fun d' => EighArenas.holds_of_forall_read_eq (H := H) (p := p) (M := M) (n := n)
    (F := F) (ℓ₀ := ℓ₀) (D := D) (d := d') (R₀ := R₀) (β := β) (root := ⟨n, A, R₀, ε, ℓ₀⟩)
    (sem := I.sem) hrd
  have hH₂ : H.Shaped st₂.store p n D := EighArenas.Shaped.of_shape_eq (fun x hx => by
    rw [hm₁.1]
    exact Store.getElem?_shape_push_of_lt _ (by have := hlt x hx; omega)) hH
  have htH : b ∉ H.handles := fun h => lt_irrefl _ (hlt b h)
  refine (RoutineSpec.forRange_const (m := md) (I := I) (n := .const n)
    (body := fun lo => eighUpSlot p mm n d lo b H)
    (pre := fun st₀ => st₀.store.read p b 0 = some (M.div (eighLevelParams M R₀ ε ℓ₀ d).1
        (M.ofNat 2)) ∧ st₀.store.read p b 1 = some (M.neg (M.div
        (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2))) ∧
      H.LevelHolds I.sem st₀.store p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      H.RecordHolds I.sem st₀.store p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      H.OutHolds st₀.store p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) ∧
      H.Shaped st₀.store p n D)
    [(H.Ua, 2 * (n * n) * d, 2 * (n * n)), (H.Ea, n * d, n)]
    (fun st₀ k st => H.UpSlotsDone st st₀ p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d k)
    (fun st _ => ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    (fun st₀ hpre lo hlo => spec_eighUpSlot hmm md hsem p n ℓ₀ F d D hd H b (by simpa using hlo)
      hnd htH hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1
      (Mode.needs_of hpre.2.2.2.2.2 md))).wp_run
    ⟨ht0, ht1, (hT d).1 hlev, (hT d).2.1 hrec, (hT (d + 1)).2.2 hout, hH₂⟩ fun st₃ hm₃ hinv => ?_
  refine ⟨(hm₁.trans hm₃).of_sub fun x hx => ?_, fun st₁ _ heq => ?_⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl) | rfl | rfl
    · exact ⟨(b, 0, (2 : IExp ℕ).eval), by simp, rfl, le_rfl, by simp⟩
    · exact ⟨(b, 0, (2 : IExp ℕ).eval), by simp, rfl, by simp, by simp⟩
    · exact ⟨(H.Ua, 2 * (n * n) * d, 2 * (n * n)), by simp, rfl, le_rfl, le_rfl⟩
    · exact ⟨(H.Ea, n * d, n), by simp, rfl, le_rfl, le_rfl⟩
  · have hsz3 : st₃.store.size = b + 1 := by
      rw [Store.size_eq_of_shape_eq (hinv.1.trans hm₁.1), St.size_allocate, hsz]
    exact ⟨outHolds_release_of_upSlotsDone hinv (fun x hx => by have := hlt x hx; omega),
      (hinv.2.1.trans hp₁).trans (congrArg (·.pos) heq)⟩

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
  obtain ⟨hUE, -⟩ := H.ua_ne_ea_and_of_nodup hH.1
  obtain ⟨hm, hO, hp⟩ := (spec_eighUpLevel hmm .liberal (u := fun _ => 0) trivial p n ℓ₀ F d D
    hd hlit H (b := st.store.size) (two := two)).spec.holds_of_exec ⟨rfl, hH, htwov, hlev, hrec,
    hout⟩ h
  exact ⟨hO, fun q b i hb => hm.2 q b i (by unfold EighArenas.LevelCell at hb; fp_omega [hb, hUE]),
    hm.1, hp⟩

end NLAlib
