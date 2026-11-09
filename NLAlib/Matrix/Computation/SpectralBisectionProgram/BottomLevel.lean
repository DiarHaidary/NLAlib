/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownSlot

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

/-- The slot of the spent level: the node at the slot $lo$ (if any) gets the stored identity and
zero eigenvalues. It is the body of the loop of `NLAlib.eighBottomLevel`. -/
def eighBottomSlot (p : P) (n D : IExp ℕ) (Ua Ea Sz : ℕ) (lo : ℕ) : Builder P ι ℕ ℕ Unit :=
  Builder.bindIdx p ⟨Sz, eighSlotOff n D (.var lo)⟩ (n - .var lo) fun k =>
    eighWhen (.var k) do
      zidentity p (.var k) Ua (eighBlockOff n D (.var lo))
      forRange (.var k) fun i => ins (.lit p ⟨Ea, eighSlotOff n D (.var lo) + .var i⟩ 0)

/-- The junk output of a node as a routine specification: the stored identity in the node's
block of `Ua` and zeros in its cells of `Ea`; the run modifies only these blocks and keeps the
tape positions; in mode `total` it also succeeds, given the literals $0$ and $1$ and the blocks
writable. No printed source. -/
theorem spec_eighBottomNode (md : Mode) (p : P) (n D lo k : ℕ) {Ua Ea : ℕ} (hUE : Ua ≠ Ea) :
    RoutineSpec md I (fun st => md.Needs ((∃ v, I.sem.lit p 0 = some v) ∧
        (∃ v, I.sem.lit p 1 = some v) ∧
        Writable st.store p Ua (2 * (n * n) * D + 2 * n * lo) (2 * (k * k)) ∧
        Writable st.store p Ea (n * D + lo) k))
      (do
        zidentity (ι := ι) p (.var k) Ua (eighBlockOff (.const n) (.const D) (.var lo))
        forRange (.var k) fun i =>
          ins (.lit p ⟨Ea, eighSlotOff (.const n) (.const D) (.var lo) + .var i⟩ 0))
      [(Ua, 2 * (n * n) * D + 2 * n * lo, 2 * (k * k)), (Ea, n * D + lo, k)]
      fun st st' => pairLayout.Holds st'.store p Ua (2 * (n * n) * D + 2 * n * lo)
          ((eighTapeMachine I p mmR qrR).identityMat k) ∧
        (∀ i : Fin k, st'.store.read p Ea (n * D + lo + i) =
          some (eighTapeMachine I p mmR qrR).zero) ∧ PosKept st st' := by
  have h1 := spec_zidentity (I := I) (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR)
    (qrR := qrR) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) md p k (Y := Ua)
    (yo := eighBlockOff (.const n) (.const D) (.var lo))
  have h1' := h1.congr (r' := zidentity (ι := ι) p (.var k) Ua
    (eighBlockOff (.const n) (.const D) (.var lo))) (by exec_composable)
    fun st => exec_zidentity_congr I p st (.var k) Ua _
  have h2 := spec_forRange_lit (m := md) (I := I) (p := p) (q := 0) (n := .var k) (Y := Ea)
    (off := n * D + lo) (didx := fun i => eighSlotOff (.const n) (.const D) (.var lo) + .var i)
    fun i => by simp [eighSlotOff]
  have e1 : (eighBlockOff (.const n) (.const D) (.var lo)).eval = 2 * (n * n) * D + 2 * n * lo := by
    simp [eighBlockOff]
  have e2 : (IExp.var k : IExp ℕ).eval = k := rfl
  have h1'' := h1'.conseq (pre' := fun st => md.Needs ((∃ v, I.sem.lit p 0 = some v) ∧
      (∃ v, I.sem.lit p 1 = some v) ∧
      Writable st.store p Ua (2 * (n * n) * D + 2 * n * lo) (2 * (k * k)) ∧
      Writable st.store p Ea (n * D + lo) k))
    (fun st hN => hN.mono fun h => ⟨h.1, h.2.1, by simpa [e1] using h.2.2.1⟩) (fun _ h => h)
    fun _ _ _ h => h
  have h2' : RoutineSpec md I _ _ _ _ := ⟨h2.composable, h2.spec.with_modifies⟩
  refine (RoutineSpec.bind h1'' h2' ?_).conseq (fun _ h => h) ?_ ?_
  · intro st st₁ hN hm hp
    exact hN.mono fun h => ⟨h.1, by simpa using h.2.2.2.of_modifies hm⟩
  · intro x hx
    rw [e1] at hx
    exact hx
  · intro st st' hN ⟨st₁, ⟨hU, hp₁⟩, hm₂, hz, hp₂⟩
    refine ⟨?_, fun i => ?_, hp₂.trans hp₁⟩
    · rw [e1] at hU
      refine (readsOnly_pairLayoutHolds p Ua (2 * (n * n) * D + 2 * n * lo) _).of_modifies hU hm₂ ?_
      fp_omega [hUE]
    · obtain ⟨v, hv, hr⟩ := hz i i.2
      simp [eighTapeMachine, ScalarSem.toFloatMachine, hv, hr]

omit [Inhabited K] in
/-- A held block of zero rows is trivially held. -/
theorem pairLayout_holds_zero {s : Store P K} {p : P} {b off : ℕ}
    (A : Matrix (Fin 0) (Fin 0) (K × K)) : pairLayout.Holds s p b off A := fun i => i.elim0

/-- The spent level at one slot, as a routine specification: the slot's stored size $k$ (read
from `Sz`, converting to $k \le n - lo$) gives the node's junk output
(`NLAlib.spec_eighBottomNode`), and nothing for $k = 0$. No printed source. -/
theorem spec_eighBottomSlot (md : Mode) (p : P) (n D lo k : ℕ) {Ua Ea Sz : ℕ} (hUE : Ua ≠ Ea)
    (v : K) (hv : I.sem.toNat p v = some k) (hk : k ≤ n - lo) :
    RoutineSpec md I (fun st => st.store.read p Sz (n * D + lo) = some v ∧
        md.Needs ((∃ v, I.sem.lit p 0 = some v) ∧ (∃ v, I.sem.lit p 1 = some v) ∧
          Writable st.store p Ua (2 * (n * n) * D + 2 * n * lo) (2 * (k * k)) ∧
          Writable st.store p Ea (n * D + lo) k))
      (eighBottomSlot (ι := ι) p (.const n) (.const D) Ua Ea Sz lo)
      [(Ua, 2 * (n * n) * D + 2 * n * lo, 2 * (k * k)), (Ea, n * D + lo, k)]
      fun st st' => pairLayout.Holds st'.store p Ua (2 * (n * n) * D + 2 * n * lo)
          ((eighTapeMachine I p mmR qrR).identityMat k) ∧
        (∀ i : Fin k, st'.store.read p Ea (n * D + lo + i) =
          some (eighTapeMachine I p mmR qrR).zero) ∧ PosKept st st' := by
  have hn := spec_eighBottomNode (I := I) (mmR := mmR) (qrR := qrR) md p n D lo k hUE
  have hw := spec_eighWhen (I := I) (m := md) (e := (.var k : IExp ℕ)) (fun _ => hn.spec)
  unfold eighBottomSlot
  refine RoutineSpec.conseq (RoutineSpec.bindIdx_of_read
    (x := ⟨Sz, eighSlotOff (.const n) (.const D) (.var lo)⟩) (bound := .const n - .var lo)
    (v := v) (k := k) (fun st hst => by simpa [eighSlotOff] using hst.1) hv
    (Mode.needs_of (by simpa using hk) md) (fun _ => hw.spec) (fun st hst => hst.2))
    (fun _ h => h) (fun x hx => hx) ?_
  rintro st st' - ⟨-, h0, hpos⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · obtain rfl := h0 rfl
    exact ⟨pairLayout_holds_zero _, fun i => i.elim0, rfl⟩
  · exact hpos hk0

/-- The junk outputs of the nodes of depth $D$ at the slots below `w` are written. -/
def EighBottomDone (H : EighArenas) (s : Store P K) (p : P) (M : FloatMachine K ℕ ℕ)
    (n F D : ℕ) (R₀ β : K) (root : EighNode K) (w : ℕ) : Prop :=
  ∀ (a : List Bool) (lo : ℕ) (y : EighNode K), a.length = D →
    eighLoc M n F R₀ β 0 0 root a = some (lo, y) → lo < w →
      pairLayout.Holds s p H.Ua (2 * (n * n) * D + 2 * n * lo) (M.identityMat y.k) ∧
        ∀ i : Fin y.k, s.read p H.Ea (n * D + lo + i) = some M.zero

/-- The invariant of the loop of the spent level after the slots below `w`, from the state
`st₀`: the tape positions, the shape and the size cells are kept, and the junk outputs of the
slots below `w` are written. -/
def EighBottomInv (H : EighArenas) (p : P) (M : FloatMachine K ℕ ℕ) (n F D : ℕ) (R₀ β : K)
    (root : EighNode K) (st₀ st : St P K C) (w : ℕ) : Prop :=
  PosKept st₀ st ∧ st.store.shape = st₀.store.shape ∧
    (∀ q i, st.store.read q H.Sz i = st₀.store.read q H.Sz i) ∧
    EighBottomDone H st.store p M n F D R₀ β root w

/-- One slot of the spent level keeps the invariant `NLAlib.EighBottomInv`, and modifies only the
output and eigenvalue cells of depth $D$. -/
private theorem spec_eighBottomStep (md : Mode) (p : P) (n F D lo k : ℕ) (H : EighArenas)
    {root : EighNode K} {R₀ β : K} {st₀ : St P K C} {v : K}
    (hH : H.Shaped st₀.store p n D) (hv : I.sem.toNat p v = some k)
    (hvr : st₀.store.read p H.Sz (n * D + lo) = some v) (hlo : lo < n) (hk : k ≤ n - lo)
    (hN : md.Needs ((∃ v, I.sem.lit p 0 = some v) ∧ (∃ v, I.sem.lit p 1 = some v)))
    (hnew : ∀ (a : List Bool) (y : EighNode K), a.length = D →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 root a = some (lo, y) → y.k = k)
    (hdisj : ∀ (a : List Bool) (y : EighNode K) (lo' : ℕ), a.length = D →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 root a = some (lo', y) → lo' < lo →
        k = 0 ∨ lo' + y.k ≤ lo) :
    Spec md I (fun st => EighBottomInv H p (eighTapeMachine I p mmR qrR) n F D R₀ β root st₀ st lo)
      (eighBottomSlot (ι := ι) p (.const n) (.const D) H.Ua H.Ea H.Sz lo).run
      [(H.Ua, 2 * (n * n) * D, 2 * (n * n)), (H.Ea, n * D, n)]
      fun _ st' => EighBottomInv H p (eighTapeMachine I p mmR qrR) n F D R₀ β root st₀ st'
        (lo + 1) := by
  obtain ⟨hnd, -, hUa, -, hEa, -, -⟩ := hH
  have hUE : H.Ua ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hnd
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right _ hkn
  have hlk : 2 * n * lo + 2 * (n * k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) (show lo + k ≤ n by omega)
    nlinarith
  have e1 : 2 * (n * n) * D + 2 * (n * n) ≤ 2 * (n * n) * (D + 1) := le_of_eq (by ring)
  have e2 : n * D + n ≤ n * (D + 1) := le_of_eq (by ring)
  have hslot := (spec_eighBottomSlot (I := I) (mmR := mmR) (qrR := qrR) (Sz := H.Sz) md p n D
    lo k hUE v hv hk).spec.with_modifies
  refine (hslot.sub (fp' := [(H.Ua, 2 * (n * n) * D, 2 * (n * n)), (H.Ea, n * D, n)])
    fun x hx => ?_).conseq (fun st ⟨_, hsh, hSz, _⟩ => ⟨(hSz _ _).trans hvr, hN.mono fun h =>
      ⟨h.1, h.2, writable_of_shape_eq hsh hUa (by nlinarith),
        writable_of_shape_eq hsh hEa (by nlinarith)⟩⟩)
    (fun x hx => hx) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl
    · refine ⟨(H.Ua, 2 * (n * n) * D, 2 * (n * n)), Or.inl rfl, rfl, ?_, ?_⟩ <;> dsimp only <;>
        nlinarith
    · refine ⟨(H.Ea, n * D, n), Or.inr rfl, rfl, ?_, ?_⟩ <;> dsimp only <;> omega
  · rintro st st' ⟨hps, hsh, hSz, hdone⟩ ⟨hm, hU, hE, hp⟩
    have hSU : H.Sz ≠ H.Ua := fun h => by simp [EighArenas.handles, h] at hnd
    have hSE : H.Sz ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hnd
    refine ⟨hp.trans hps, hm.1.trans hsh, fun q i => ?_, fun a lo' y ha hl hlt => ?_⟩
    · exact (hm.2 q H.Sz i (by fp_omega [hSU, hSE])).trans (hSz q i)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | rfl
    · obtain ⟨h1, h2⟩ := hdone a lo' y ha hl hlt
      rcases hdisj a y lo' ha hl hlt with rfl | hd
      · refine ⟨(readsOnly_pairLayoutHolds p H.Ua _ _).of_modifies h1 hm (by
            simp [BlocksDisjoint, blockDisjoint]),
          fun i => (hm.2 p H.Ea _ (by simp [blockDisjoint])).trans (h2 i)⟩
      · have hyk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
        have hd1 : 2 * n * lo' + 2 * (y.k * y.k) ≤ 2 * n * lo := by nlinarith
        refine ⟨(readsOnly_pairLayoutHolds p H.Ua _ _).of_modifies h1 hm (by fp_omega [hUE, hd1]),
          fun i => (hm.2 p H.Ea _ (by fp_omega [hUE, i.2, hd])).trans (h2 i)⟩
    · obtain rfl := hnew a y ha hl
      exact ⟨hU, hE⟩

/-- The spent level as a routine specification: from arenas that hold the nodes of depth $D$,
the run of `NLAlib.eighBottomLevel` modifies only the output and eigenvalue cells of depth $D$,
leaves the junk outputs of `NLAlib.eighAux` at budget $0$ (`NLAlib.EighArenas.OutHolds`: the
machine's identity and zeros) and keeps the tape positions; in mode `total` it also succeeds,
given the literals $0$ and $1$. No printed source. -/
theorem spec_eighBottomLevel (md : Mode) (p : P) (n ℓ₀ F D : ℕ) (H : EighArenas)
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} :
    RoutineSpec md I (fun st => H.Shaped st.store p n D ∧
        H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ D ∧
        md.Needs ((∃ v, I.sem.lit p 0 = some v) ∧ (∃ v, I.sem.lit p 1 = some v)))
      (eighBottomLevel (ι := ι) p (.const n) (.const D) H.Ua H.Ea H.Sz)
      [(H.Ua, 2 * (n * n) * D, 2 * (n * n)), (H.Ea, n * D, n)]
      fun st st' => H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F D R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ D ∧ PosKept st st' := by
  unfold eighBottomLevel
  refine RoutineSpec.conseq (RoutineSpec.forRange_const
    (body := eighBottomSlot (ι := ι) p (.const n) (.const D) H.Ua H.Ea H.Sz) _
    (fun st₀ w st => EighBottomInv H p (eighTapeMachine I p mmR qrR) n F D R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ st₀ st w)
    (fun st _ => ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    ?_) (fun _ h => h) (fun x hx => hx) ?_
  · rintro st₀ ⟨hH, hlev, hN⟩ lo hlo
    change lo < n at hlo
    by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = D ∧
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
    · obtain ⟨a, y, ha, hay⟩ := hy
      obtain ⟨v, hvr, hv⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hay).1
      have hb := eighLoc_bounds (by omega : 1 ≤ n) hay
      exact spec_eighBottomStep md p n F D lo y.k H hH hv hvr hlo (by omega) hN
        (fun a' y' ha' hay' => by rw [eighLoc_eq_of_slot (by omega) (ha.trans ha'.symm) hay hay'])
        fun a' y' lo' ha' hay' hlt => Or.inr
          (le_of_eighLoc_lt (ha'.trans ha.symm) hay hay' hlt)
    · push Not at hy
      obtain ⟨v, hvr, hv⟩ := Option.bind_eq_some_iff.mp (hlev.2.1 lo hlo fun a y ha => hy a y ha)
      exact spec_eighBottomStep md p n F D lo 0 H hH hv hvr hlo (Nat.zero_le _) hN
        (fun a' y' ha' hay' => absurd hay' (hy a' y' ha')) fun _ _ _ _ _ _ => Or.inl rfl
  · rintro st₀ st' - ⟨hps, -, -, hdone⟩
    refine ⟨fun a lo y ha hay => ?_, hps⟩
    rw [Nat.sub_self]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hy0 : y.k = 0 := by
        cases a with
        | nil => cases hay; rfl
        | cons b a => simp [eighLoc, eighStep] at hay
      exact ⟨fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega)⟩
    · exact hdone a lo y ha hay (by have := eighLoc_bounds hn hay; change lo < n; omega)

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell outside the output and eigenvalue blocks of depth $D$ is disjoint from the footprint
of the spent level. -/
theorem blockDisjoint_eighBottomFp {H : EighArenas} {n D b i : ℕ} (hUE : H.Ua ≠ H.Ea)
    (hb : ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i)) :
    ∀ x ∈ [(H.Ua, 2 * (n * n) * D, 2 * (n * n)), (H.Ea, n * D, n)],
      blockDisjoint (b, i, 1) x = true := by
  unfold EighArenas.LevelCell at hb
  fp_omega [hb, hUE]

/-- The spent level writes the junk outputs: under exact integer literals up to $n + 4$, a
successful run of `NLAlib.eighBottomLevel` at depth $D$ from a state whose
arenas hold the nodes of depth $D$ ends with the outputs of depth $D$ holding `NLAlib.eighAux` at
budget $0$ (`NLAlib.EighArenas.OutHolds` at $D$: the machine's identity and zeros); every cell
outside the output and eigenvalue arenas at depth $D$ is unchanged, the store shape and the tape
positions too. No printed source. -/
theorem holds_of_exec_eighBottomLevel {dec : P → K → ℝ} (p : P) (n ℓ₀ F D : ℕ)
    (_hlit : IsExactIntLit dec I.sem (n + 4)) (H : EighArenas)
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
  have hUE : H.Ua ≠ H.Ea := fun e => by have hnd := hH.1; simp [EighArenas.handles, e] at hnd
  obtain ⟨hm, hout, hp⟩ := (spec_eighBottomLevel (I := I) (mmR := mmR) (qrR := qrR) .liberal p n
    ℓ₀ F D H).spec.holds_of_exec ⟨hH, hlev, trivial⟩ h
  exact ⟨hout, fun q b i hb => hm.2 q b i (blockDisjoint_eighBottomFp hUE hb), hm.1, hp⟩

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
  obtain ⟨st', h, -⟩ := (spec_eighBottomLevel (I := I) (mmR := mmR) (qrR := qrR) .total p n ℓ₀ F
    D H).spec.exists_exec ⟨hH, hlev, hsem.lit_ok p 0 trivial, hsem.lit_ok p 1 trivial⟩
  exact ⟨st', h⟩

end NLAlib
