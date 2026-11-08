/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownLevel

/-!
# The spent level of the spectral bisection program

The spent level of `NLAlib.eighProg` (`NLAlib.eighBottomLevel`), below the last depth, writes the
junk outputs of the nodes that remain (`NLAlib.EighArenas.OutHolds`), and always succeeds.

## Main results

* `NLAlib.holds_of_exec_eighBottomLevel`, `NLAlib.exists_exec_eighBottomLevel`: the spent level.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

omit [Inhabited K] in
/-- A successful loop of literals into the cells `f w` of one buffer keeps the shape and the tape
positions, leaves the literal in every written cell and every other cell unchanged. -/
private theorem read_of_exec_loop_lit {p : P} {m : IExp ℕ} {Y : ℕ} {f : ℕ → IExp ℕ} {c : ℚ}
    {st st' : St P K C}
    (h : exec I (.loop m fun w => .seq (.instr (.lit p ⟨Y, f w⟩ c)) .skip) st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ w < m.eval, ∃ z, I.sem.lit p c = some z ∧ st'.store.read p Y (f w).eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w < m.eval, (f w).eval ≠ i) →
        st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧
      (∀ w' < w, ∃ z, I.sem.lit p c = some z ∧ s.store.read p Y (f w').eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w' < w, (f w').eval ≠ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun w' hw => ?_,
    fun q b i hb => ?_⟩
  · by_cases hww : (f w').eval = (f w).eval
    · exact ⟨v, hv, hww ▸ Store.read_of_write_eq_some hw'⟩
    · have hlt : w' < w := lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) (fun h => hww (h ▸ rfl))
      rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr hww)]
      exact hrd w' hlt
  · rw [Store.read_of_write_eq_some_of_ne hw' ?_]
    · exact hfr q b i (hb.imp_right fun h w' hw => h w' (Nat.lt_succ_of_lt hw))
    · exact hb.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

/-- The run of the spent level at a node of size $k$ at slot $lo$: the stored identity in its
output block, zeros in its eigenvalue cells, every other cell, the shape and the positions kept. -/
private theorem eighBottomLevel_node_run (p : P) (n D lo k : ℕ) (H : EighArenas)
    {s₀ s₂ : St P K C} (hUE : H.Ua ≠ H.Ea)
    (h : exec I (do
        zidentity (ι := ι) p (.var k) H.Ua (eighBlockOff (.const n) (.const D) (.var lo))
        forRange (.var k) fun i =>
          ins (.lit p ⟨H.Ea, eighSlotOff (.const n) (.const D) (.var lo) + IExp.var i⟩ 0)).run s₀ =
      some s₂) :
    s₂.store.shape = s₀.store.shape ∧ s₂.pos = s₀.pos ∧
      pairLayout.Holds s₂.store p H.Ua (2 * (n * n) * D + 2 * n * lo)
        ((eighTapeMachine I p mmR qrR).identityMat k) ∧
      (∀ i : Fin k, s₂.store.read p H.Ea (n * D + lo + i) =
        some (eighTapeMachine I p mmR qrR).zero) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * D + 2 * n * lo ∨
        2 * (n * n) * D + 2 * n * lo + 2 * (k * k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * D + lo ∨ n * D + lo + k ≤ i) →
        s₂.store.read q b i = s₀.store.read q b i := by
  rw [exec_run_bind I (b := zidentity (ι := ι) p (.var k) H.Ua
    (eighBlockOff (.const n) (.const D) (.var lo))) (fun _ => rfl)] at h
  obtain ⟨s₄, hz, h⟩ := Option.bind_eq_some_iff.mp h
  have hU := (holds_of_exec_zidentity (mmR := mmR) (qrR := qrR)
    (toNat := fun x => (I.sem.toNat p x).getD 0) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) p k
    ((exec_zidentity_congr I p _ _ _ _).symm.trans hz)).1
  change exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) .skip))) .skip) _ = _ at hz
  rw [exec_seq_skip, exec_named, exec_seq] at hz
  obtain ⟨σ, h₀, h₁⟩ := Option.bind_eq_some_iff.mp hz
  rw [exec_seq_skip] at h₁
  change exec I (.seq (.loop _ _) .skip) _ = _ at h
  rw [exec_seq_skip] at h
  obtain ⟨hsh₀, hps₀, -, hfr₀⟩ := read_of_exec_loop_lit h₀
  obtain ⟨hsh₁, hps₁, -, hfr₁⟩ := read_of_exec_loop_lit h₁
  obtain ⟨hsh₂, hps₂, hE, hfr₂⟩ := read_of_exec_loop_lit h
  simp only [eighBlockOff, eighSlotOff, zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat,
    IExp.eval_const, IExp.eval_var] at hU hfr₀ hfr₁ hfr₂ hE
  have hF : ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * D + 2 * n * lo ∨
      2 * (n * n) * D + 2 * n * lo + 2 * (k * k) ≤ i) →
      (b ≠ H.Ea ∨ i < n * D + lo ∨ n * D + lo + k ≤ i) →
      s₂.store.read q b i = s₀.store.read q b i := by
    intro q b i hU' hE'
    rw [hfr₂ q b i (hE'.imp_right fun h w hw => by omega),
      hfr₁ q b i (hU'.imp_right fun h w hw => by
        have : w + k * w < k * k := by nlinarith
        omega),
      hfr₀ q b i (hU'.imp_right fun h w hw => by omega)]
  refine ⟨hsh₂.trans (hsh₁.trans hsh₀), hps₂.trans (hps₁.trans hps₀),
    hU.of_forall_read_eq fun i _ _ => hfr₂ p _ i (Or.inl hUE), fun i => ?_, hF⟩
  obtain ⟨z, hz, hr⟩ := hE i i.isLt
  rw [hr]
  simp only [eighTapeMachine, ScalarSem.toFloatMachine, hz, Option.getD_some]

/-- One slot of the spent level: the node at the slot (if any) gets the stored identity and zero
eigenvalues; the shape, the tape positions, every cell outside depth $D$ of the output and
eigenvalue arenas, and the outputs of the slots below are kept. -/
private theorem eighBottomLevel_step (p : P) (n ℓ₀ F D : ℕ) (H : EighArenas)
    {st s₁ s₂ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {lo : ℕ}
    (hlo : lo < n) (hH : H.Shaped st.store p n D)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ D)
    (hsh : s₁.store.shape = st.store.shape) (hps : s₁.pos = st.pos)
    (hfr : ∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i) →
      s₁.store.read q b i = st.store.read q b i)
    (hdone : ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = D →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
      lo' < lo →
      pairLayout.Holds s₁.store p H.Ua (2 * (n * n) * D + 2 * n * lo')
          ((eighTapeMachine I p mmR qrR).identityMat y.k) ∧
        ∀ i : Fin y.k, s₁.store.read p H.Ea (n * D + lo' + i) =
          some (eighTapeMachine I p mmR qrR).zero)
    (h : exec I (Builder.bindIdx (ι := ι) p ⟨H.Sz, eighSlotOff (.const n) (.const D) (.var lo)⟩
      (.const n - .var lo) fun k => eighWhen (.var k) do
        zidentity p (.var k) H.Ua (eighBlockOff (.const n) (.const D) (.var lo))
        forRange (.var k) fun i =>
          ins (.lit p ⟨H.Ea, eighSlotOff (.const n) (.const D) (.var lo) + .var i⟩ 0)).run s₁ =
      some s₂) :
    s₂.store.shape = st.store.shape ∧ s₂.pos = st.pos ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i) →
        s₂.store.read q b i = st.store.read q b i) ∧
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = D →
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
        lo' < lo + 1 →
        pairLayout.Holds s₂.store p H.Ua (2 * (n * n) * D + 2 * n * lo')
            ((eighTapeMachine I p mmR qrR).identityMat y.k) ∧
          ∀ i : Fin y.k, s₂.store.read p H.Ea (n * D + lo' + i) =
            some (eighTapeMachine I p mmR qrR).zero := by
  obtain ⟨hnd, -, -, -, -, -, -⟩ := hH
  simp only [EighArenas.handles, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s₁ = some s₂ at h
  rw [exec_seq_skip] at h
  have hSzfr : ∀ q i, s₁.store.read q H.Sz i = st.store.read q H.Sz i := fun q i =>
    hfr q _ i (fun h => h.1.elim (fun e => hnd.2.1.2.2.1 e.symm) (fun e => hnd.2.2.2.1.1 e.symm))
  by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = D ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
  swap
  · push Not at hy
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.2.1 lo hlo fun a y ha => hy a y ha)
    rw [exec_bindIdx_of_read I ((hSzfr p _).trans hv) hk (Nat.zero_le _)] at h
    change exec I (.seq (.loop _ _) .skip) _ = some s₂ at h
    rw [exec_seq_skip, exec_loop] at h
    simp only [IExp.eval_sub, IExp.eval_one, IExp.eval_var, Nat.sub_zero,
      Nat.sub_self, List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    refine ⟨hsh, hps, hfr, fun a lo' y ha hay hlt =>
      hdone a lo' y ha hay (lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) ?_)⟩
    rintro rfl
    exact hy a y ha hay
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hay).1
  have hb := eighLoc_bounds (by omega : 1 ≤ n) hay
  rw [exec_bindIdx_of_read I ((hSzfr p _).trans hv) hk
    (by simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var]; omega)] at h
  change exec I (.seq (.loop _ _) .skip) _ = some s₂ at h
  rw [exec_seq_skip, exec_loop] at h
  rw [show (1 - (1 - IExp.var y.k) : IExp ℕ).eval = 1 by
    simp only [IExp.eval_sub, IExp.eval_one, IExp.eval_var]; omega, List.range_one,
    List.foldlM_cons] at h
  simp only [List.foldlM_nil, bind_pure] at h
  have hUE : H.Ua ≠ H.Ea := hnd.2.1.2.1
  obtain ⟨hsh₂, hps₂, hU, hE, hF⟩ := eighBottomLevel_node_run p n D lo y.k H hUE h
  have hkn : y.k ≤ n := by omega
  have hblk : 2 * n * lo + 2 * (y.k * y.k) ≤ 2 * (n * n) := by
    nlinarith [Nat.mul_le_mul_left n hb.2, Nat.mul_le_mul_right y.k hkn]
  refine ⟨hsh₂.trans hsh, hps₂.trans hps,
    fun q b i hb' => (hF q b i ?_ ?_).trans (hfr q b i hb'), ?_⟩
  · by_contra hc
    push Not at hc
    refine hb' ⟨Or.inl hc.1, Or.inl ⟨Or.inr (Or.inl hc.1), by omega, ?_⟩⟩
    rw [Nat.mul_succ]
    omega
  · by_contra hc
    push Not at hc
    refine hb' ⟨Or.inr hc.1, Or.inr (Or.inl ⟨Or.inl hc.1, by omega, ?_⟩)⟩
    rw [Nat.mul_succ]
    omega
  intro a' lo' y' ha' hay' hlt
  have hb' := eighLoc_bounds (by omega : 1 ≤ n) hay'
  by_cases haa : a' = a
  · subst haa
    rw [hay] at hay'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hay')
    exact ⟨hU, hE⟩
  have hdis := eighLoc_disjoint (ha'.trans ha.symm) haa hay' hay
  have hlt' : lo' + y'.k ≤ lo := by omega
  obtain ⟨hU', hE'⟩ := hdone a' lo' y' ha' hay' (by omega)
  refine ⟨hU'.of_forall_read_eq fun i _ hi => hF p _ i (Or.inr (Or.inl ?_)) (Or.inl hUE),
    fun i => (hF p _ _ (Or.inl hUE.symm) (Or.inr (Or.inl (by omega)))).trans (hE' i)⟩
  change i < _ + y'.k * y'.k * 2 at hi
  nlinarith [Nat.mul_le_mul_left n hlt', Nat.mul_le_mul_right y'.k (by omega : y'.k ≤ n)]

/-- The spent level writes the junk outputs: under exact integer literals up to $n + 4$, a
successful run of `NLAlib.eighBottomLevel` at depth $D$ from a state whose
arenas hold the nodes of depth $D$ ends with the outputs of depth $D$ holding `NLAlib.eighAux` at
budget $0$ (`NLAlib.EighArenas.OutHolds` at $D$: the machine's identity and zeros); every cell
outside the output and eigenvalue arenas at depth $D$ is unchanged, the store shape and the tape
positions too. No printed source. -/
theorem holds_of_exec_eighBottomLevel {dec : P → K → ℝ} (p : P) (n ℓ₀ F D : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (H : EighArenas)
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ D)
    (h : exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) H.Ua H.Ea H.Sz).run st =
      some st') :
    H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ D ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  change exec I (.seq (.loop (.const n) _) .skip) st = some st' at h
  rw [exec_seq_skip] at h
  obtain ⟨hsh, hps, hfr, hdone⟩ := forall_of_exec_loop_eq_some I (n := .const n)
    (fun lo s => s.store.shape = st.store.shape ∧ s.pos = st.pos ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i) →
        s.store.read q b i = st.store.read q b i) ∧
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = D →
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
        lo' < lo →
        pairLayout.Holds s.store p H.Ua (2 * (n * n) * D + 2 * n * lo')
            ((eighTapeMachine I p mmR qrR).identityMat y.k) ∧
          ∀ i : Fin y.k, s.store.read p H.Ea (n * D + lo' + i) =
            some (eighTapeMachine I p mmR qrR).zero)
    ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun lo hlo s₁ s₂ ⟨hsh, hps, hfr, hdone⟩ hex =>
      eighBottomLevel_step p n ℓ₀ F D H hlo hH hlev hsh hps hfr hdone hex) h
  refine ⟨fun a lo y ha hay => ?_, hfr, hsh, hps⟩
  rw [Nat.sub_self]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- the root of size 0 is a leaf, so it is the only node, and its blocks are empty
    have hy0 : y.k = 0 := by
      cases a with
      | nil => cases hay; rfl
      | cons b a => simp [eighLoc, eighStep] at hay
    have hk : ∀ i : Fin y.k, False := fun i => absurd i.isLt (by omega)
    exact ⟨fun i => (hk i).elim, fun i => (hk i).elim⟩
  have hb := eighLoc_bounds hn hay
  exact hdone a lo y ha hay (by simp only [IExp.eval_const]; omega)

omit [Inhabited K] in
/-- A loop of literals into cells of one buffer inside its shape succeeds and keeps the shape and
every other buffer. -/
private theorem exists_exec_loop_lit_of_lt {p : P} {m : IExp ℕ} {Y len : ℕ} {f : ℕ → IExp ℕ}
    {c : ℚ} {st : St P K C} (hc : ∃ z, I.sem.lit p c = some z)
    (hY : st.store.shape[Y]? = some (p, len)) (hf : ∀ w < m.eval, (f w).eval < len) :
    ∃ st', exec I (.loop m fun w => .seq (.instr (.lit p ⟨Y, f w⟩ c)) .skip) st = some st' ∧
      st'.store.shape = st.store.shape ∧
      ∀ q b i, b ≠ Y → st'.store.read q b i = st.store.read q b i := by
  obtain ⟨z, hz⟩ := hc
  refine exists_exec_loop_eq_some_of_forall (I := I) (fun _ s => s.store.shape = st.store.shape ∧
      ∀ q b i, b ≠ Y → s.store.read q b i = st.store.read q b i) ⟨rfl, fun _ _ _ _ => rfl⟩ ?_
  rintro w hw s ⟨hsh, hrd⟩
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := s.store) z
    (hsh ▸ hY) (hf w hw)
  refine ⟨_, (exec_seq_instr_lit I hz hs').trans (exec_skip I _), ?_, fun q b i hb => ?_⟩
  · exact (Store.shape_of_write_eq_some hs').trans hsh
  · exact (Store.read_of_write_eq_some_of_ne hs' (Or.inl hb)).trans (hrd q b i hb)

/-- The spent level succeeds under the standard model with every value in range, when the
arenas are allocated and their size cells of depth $D$ are initialised. No printed source. -/
theorem exists_exec_eighBottomLevel {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n ℓ₀ F D : ℕ) (H : EighArenas) {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hH : H.Shaped st.store p n D)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ D) :
    ∃ st', exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) H.Ua H.Ea H.Sz).run st =
      some st' := by
  obtain ⟨hnd, -, hUa, -, hEa, hSz, -⟩ := hH
  simp only [EighArenas.handles, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  change ∃ st', exec I (.seq (.loop (.const n) _) .skip) st = some st'
  simp only [exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall (I := I)
    (fun _ s => s.store.shape = st.store.shape ∧
      ∀ q i, s.store.read q H.Sz i = st.store.read q H.Sz i) ⟨rfl, fun _ _ => rfl⟩ ?_).imp
    fun _ h => h.1
  rintro lo hlo s ⟨hsh, hrd⟩
  simp only [IExp.eval_const] at hlo
  -- the size cell of the slot reads an index
  obtain ⟨v, hv, k, hk, hkn⟩ : ∃ v, st.store.read p H.Sz (n * D + lo) = some v ∧
      ∃ k, I.sem.toNat p v = some k ∧ k ≤ n - lo := by
    have : ∃ k, ReadsIdx I.sem st.store p H.Sz (n * D + lo) k ∧ k ≤ n - lo := by
      by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = D ∧
          eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
      · obtain ⟨a, y, ha, hy⟩ := hy
        obtain ⟨-, hb⟩ := eighLoc_bounds (by omega : 1 ≤ n) hy
        exact ⟨_, (hlev.1 a lo y ha hy).1, by omega⟩
      · push Not at hy
        exact ⟨0, hlev.2.1 lo hlo fun a y ha => hy a y ha, Nat.zero_le _⟩
    obtain ⟨k, hk, hkn⟩ := this
    unfold ReadsIdx at hk
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hk
    exact ⟨v, hv, k, hk, hkn⟩
  have hx : s.store.read p H.Sz (n * D + lo) = some v := (hrd p _).trans hv
  change ∃ st', exec I (.seq (.bindIdx p ⟨H.Sz, eighSlotOff (.const n) (.const D) (.var lo)⟩
    (.const n - .var lo) _) .skip) s = some st' ∧ _
  rw [exec_seq_skip, exec_bindIdx_of_read I hx hk (by exact hkn)]
  have hk' : k ≤ n - lo := hkn
  generalize k = k' at hk' ⊢
  change ∃ st', exec I (.seq (.loop _ fun _ => _) .skip) _ = some st' ∧ _
  rw [exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall (I := I)
    (fun _ s => s.store.shape = st.store.shape ∧
      ∀ q i, s.store.read q H.Sz i = st.store.read q H.Sz i) ⟨hsh, hrd⟩ ?_
  rintro - - s₁ ⟨hsh₁, hrd₁⟩
  have hlit : ∀ c : ℚ, ∃ z, I.sem.lit p c = some z := fun c => hsem.lit_ok p c trivial
  have hblk : 2 * n * lo + 2 * (k' * k') ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul hk' hk'
    have h2 : n - lo + lo = n := Nat.sub_add_cancel hlo.le
    nlinarith
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) .skip)))
    (.seq (.loop _ _) .skip)) s₁ = some st' ∧ _
  obtain ⟨s₂, h₂, hsh₂, hrd₂⟩ := exists_exec_loop_lit_of_lt (I := I)
    (m := 2 * (.var k' * .var k')) (Y := H.Ua)
    (f := fun w => eighBlockOff (.const n) (.const D) (.var lo) + .var w) (hlit 0)
    (hsh₁ ▸ hUa) (by
      intro w hw
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat, IExp.eval_const,
        IExp.eval_var] at hw ⊢
      nlinarith)
  obtain ⟨s₃, h₃, hsh₃, hrd₃⟩ := exists_exec_loop_lit_of_lt (I := I) (st := s₂)
    (m := .var k') (Y := H.Ua)
    (f := fun i => eighBlockOff (.const n) (.const D) (.var lo) + zidx (.var k') (.var i) (.var i))
    (hlit 1) ((hsh₂.trans hsh₁) ▸ hUa) (by
      intro i hi
      simp only [eighBlockOff, zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat,
        IExp.eval_const, IExp.eval_var] at hi ⊢
      nlinarith)
  obtain ⟨s₄, h₄, hsh₄, hrd₄⟩ := exists_exec_loop_lit_of_lt (I := I) (st := s₃)
    (m := .var k') (Y := H.Ea)
    (f := fun i => eighSlotOff (.const n) (.const D) (.var lo) + .var i)
    (hlit 0) ((hsh₃.trans (hsh₂.trans hsh₁)) ▸ hEa) (by
      intro i hi
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var] at hi ⊢
      rw [Nat.mul_succ]
      omega)
  refine ⟨s₄, ?_, hsh₄.trans (hsh₃.trans (hsh₂.trans hsh₁)), fun q i => ?_⟩
  · rw [exec_seq, exec_named, exec_seq]
    exact Option.bind_eq_some_iff.mpr ⟨s₃, Option.bind_eq_some_iff.mpr ⟨s₂, h₂, by
      rw [exec_seq_skip]; exact h₃⟩, by rw [exec_seq_skip]; exact h₄⟩
  · rw [hrd₄ q _ i (Ne.symm hnd.2.2.2.1.1), hrd₃ q _ i (Ne.symm hnd.2.1.2.2.1),
      hrd₂ q _ i (Ne.symm hnd.2.1.2.2.1)]
    exact hrd₁ q i

end NLAlib
