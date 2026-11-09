/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownSlot

/-!
# The downward level of the spectral bisection program

One level of the downward pass of `NLAlib.eighProg` (`NLAlib.eighDownLevel`) takes the arenas from
holding the nodes of depth $d$ to holding those of depth $d + 1$ and the records of depth $d$
(`NLAlib.EighArenas.LevelHolds`, `NLAlib.EighArenas.RecordHolds`), as the node step
`NLAlib.eighStep` of the machine of the interpretation computes them.

## Main results

* `NLAlib.holds_of_exec_eighDownLevel`: what a successful level computes.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! #### Helpers of the level -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The window of a slot lies in the records of depth $d$ (bases, outputs, eigenvalues, kinds,
splits) and the cells of depth $d + 1$; the sizes, node matrices and parameters of depth $d$ are
outside it. -/
private theorem levelCell_of_win {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hk1 : 1 ≤ k) (hk : lo + k ≤ n) (h : EighSlotWindow H n d lo k cs b i) :
    ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) ∨
      H.LevelCell n (d + 1) b i := by
  have e1 : 2 * n * (lo + k) ≤ 2 * (n * n) := by
    rw [show 2 * (n * n) = 2 * n * n by ring]; exact Nat.mul_le_mul_left _ hk
  have e2 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have e3 : 2 * (n * n) * (d + 1 + 1) = 2 * (n * n) * (d + 1) + 2 * (n * n) := by ring
  have e4 : n * (d + 1) = n * d + n := by ring
  have e5 : n * (d + 1 + 1) = n * (d + 1) + n := by ring
  unfold EighSlotWindow at h
  unfold EighArenas.LevelCell
  rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1⟩ | ⟨hb, j, hj1, hj2, -, hj⟩
  · refine Or.inl ⟨by rcases hb with h | h <;> simp [h],
      Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩⟩
  · exact Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)
  · exact Or.inl ⟨Or.inr (Or.inr (Or.inl hb)), Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)⟩
  · refine Or.inl ⟨by rcases hb with h | h <;> simp [h],
      Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩)⟩
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hb), by omega, by omega⟩))

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The disequalities of the arenas and the buffers `par`, `Su`, `Sg`, `c` that the downward level
uses, from their distinctness. -/
private theorem downLevel_bufs_ne {H : EighArenas} {par Su Sg c : ℕ}
    (h : (H.handles ++ [par, Su, Sg, c]).Nodup) :
    (H.Lv ≠ Su ∧ H.Lv ≠ Sg) ∧ (H.Sz ≠ Su ∧ H.Sz ≠ Sg ∧ H.Sz ≠ H.Lv) ∧
      (H.Ma ≠ Su ∧ H.Ma ≠ Sg ∧ H.Ma ≠ H.Lv) ∧ (par ≠ Su ∧ par ≠ Sg ∧ par ≠ H.Lv) ∧
      (c ≠ Su ∧ c ≠ Sg ∧ c ≠ H.Lv) ∧ Su ≠ Sg := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    intro e <;> simp [EighArenas.handles, e] at h

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The buffers `par`, `Su`, `Sg`, `c` and the window arena are none of the arenas a slot
writes, when the arenas and these buffers are distinct. -/
private theorem not_mem_slotBufs {H : EighArenas} {par Su Sg c x : ℕ}
    (h : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hx : x = par ∨ x = Su ∨ x = Sg ∨ x = c ∨ x = H.Lv) :
    x ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
  intro hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hm with e | e | e | e | e | e | e <;> simp [EighArenas.handles, e] at h

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A buffer that a slot writes is one of the arenas, so it lies below a bound of all of them. -/
private theorem lt_of_win {H : EighArenas} {tH n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hlt : ∀ x ∈ H.handles, x < tH) (hw : EighSlotWindow H n d lo k cs b i) : b < tH := by
  apply hlt
  have := mem_of_eighSlotWindow hw
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  tauto

/-! #### The blocks a level writes -/

/-- The blocks of the arenas that hold the records of depth $d$: the bases, outputs,
eigenvalues, kinds and splits. -/
def eighRecordBlocks (H : EighArenas) (n d : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(H.Qa, 2 * (n * n) * d, 2 * (n * n)), (H.Ua, 2 * (n * n) * d, 2 * (n * n)),
    (H.Ea, n * d, n), (H.Kd, n * d, n), (H.Kp, n * d, n)]

/-- The blocks of the cells of depth $d$ of the arenas (`NLAlib.EighArenas.LevelCell`). -/
def eighLevelBlocks (H : EighArenas) (n d : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(H.Ma, 2 * (n * n) * d, 2 * (n * n)), (H.Ua, 2 * (n * n) * d, 2 * (n * n)),
    (H.Qa, 2 * (n * n) * d, 2 * (n * n)), (H.Ea, n * d, n), (H.Sz, n * d, n), (H.Kd, n * d, n),
    (H.Kp, n * d, n), (H.Lv, 2 * d, 2)]

/-- The blocks the slots of the level of depth $d$ may write: the records of depth $d$, the cells
of depth $d + 1$ and the scratch cell `t[4]`. -/
def eighSlotsFp (H : EighArenas) (n d t : ℕ) : List (ℕ × ℕ × ℕ) :=
  eighRecordBlocks H n d ++ eighLevelBlocks H n (d + 1) ++ [(t, 4, 1)]

/-- The blocks the level of depth $d$ may write: the records of depth $d$, the cells of depth
$d + 1$ and the sample buffers `Su`, `Sg`. -/
def eighDownFp (H : EighArenas) (n d Su Sg : ℕ) : List (ℕ × ℕ × ℕ) :=
  eighRecordBlocks H n d ++ eighLevelBlocks H n (d + 1) ++ [(Su, 0, n), (Sg, 0, 4 * (n * n))]

/-- A cell is disjoint from a block exactly when it is not in it. -/
theorem blockDisjoint_one_iff {b i : ℕ} {x : ℕ × ℕ × ℕ} :
    blockDisjoint (b, i, 1) x = true ↔ ¬ (b = x.1 ∧ x.2.1 ≤ i ∧ i < x.2.1 + x.2.2) := by
  rw [blockDisjoint_iff]
  dsimp only
  omega

/-- A cell is disjoint from the blocks of depth $d$ exactly when it is not a cell of depth $d$. -/
theorem blockDisjoint_eighLevelBlocks_iff {H : EighArenas} {n d b i : ℕ} :
    (∀ x ∈ eighLevelBlocks H n d, blockDisjoint (b, i, 1) x = true) ↔
      ¬ H.LevelCell n d b i := by
  have e : 2 * (n * n) * d + 2 * (n * n) = 2 * (n * n) * (d + 1) := by ring
  have e' : n * d + n = n * (d + 1) := by ring
  simp only [eighLevelBlocks, EighArenas.LevelCell, List.forall_mem_cons, blockDisjoint_one_iff,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, e, e']
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ (⟨hb | hb | hb, hi⟩ | ⟨hb | hb | hb | hb, hi⟩ |
      ⟨hb, hi | hi⟩)
    exacts [h1 ⟨hb, hi⟩, h2 ⟨hb, hi⟩, h3 ⟨hb, hi⟩, h4 ⟨hb, hi⟩, h5 ⟨hb, hi⟩, h6 ⟨hb, hi⟩,
      h7 ⟨hb, hi⟩, h8 ⟨hb, by omega, by omega⟩, h8 ⟨hb, by omega, by omega⟩]
  · intro h
    exact ⟨fun hx => h (Or.inl ⟨Or.inl hx.1, hx.2⟩),
      fun hx => h (Or.inl ⟨Or.inr (Or.inl hx.1), hx.2⟩),
      fun hx => h (Or.inl ⟨Or.inr (Or.inr hx.1), hx.2⟩),
      fun hx => h (Or.inr (Or.inl ⟨Or.inl hx.1, hx.2⟩)),
      fun hx => h (Or.inr (Or.inl ⟨Or.inr (Or.inl hx.1), hx.2⟩)),
      fun hx => h (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl hx.1)), hx.2⟩)),
      fun hx => h (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr hx.1)), hx.2⟩)),
      fun hx => h (Or.inr (Or.inr ⟨hx.1, by omega⟩))⟩

/-- A cell is disjoint from the record blocks of depth $d$ exactly when it is not a record cell
of depth $d$ (the arenas distinct). -/
theorem blockDisjoint_eighRecordBlocks_iff {H : EighArenas} (hnd : H.handles.Nodup)
    {n d b i : ℕ} : (∀ x ∈ eighRecordBlocks H n d, blockDisjoint (b, i, 1) x = true) ↔
      ¬ ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) := by
  have e : 2 * (n * n) * d + 2 * (n * n) = 2 * (n * n) * (d + 1) := by ring
  have e' : n * d + n = n * (d + 1) := by ring
  simp only [eighRecordBlocks, EighArenas.LevelCell, List.forall_mem_cons, blockDisjoint_one_iff,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, e, e']
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩ ⟨hb, ⟨hb' | hb' | hb', hi⟩ | ⟨hb' | hb' | hb' | hb', hi⟩ |
      ⟨hb', hi⟩⟩
    all_goals rcases hb with hb | hb | hb | hb | hb
    all_goals first
      | exact h1 ⟨hb, hi⟩ | exact h2 ⟨hb, hi⟩ | exact h3 ⟨hb, hi⟩ | exact h4 ⟨hb, hi⟩
      | exact h5 ⟨hb, hi⟩
      | (exfalso; subst hb; simp [EighArenas.handles, hb'] at hnd)
  · intro h
    exact ⟨fun hx => h ⟨Or.inl hx.1, Or.inl ⟨Or.inr (Or.inr hx.1), hx.2⟩⟩,
      fun hx => h ⟨Or.inr (Or.inl hx.1), Or.inl ⟨Or.inr (Or.inl hx.1), hx.2⟩⟩,
      fun hx => h ⟨Or.inr (Or.inr (Or.inl hx.1)), Or.inr (Or.inl ⟨Or.inl hx.1, hx.2⟩)⟩,
      fun hx => h ⟨Or.inr (Or.inr (Or.inr (Or.inl hx.1))),
        Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl hx.1)), hx.2⟩)⟩,
      fun hx => h ⟨Or.inr (Or.inr (Or.inr (Or.inr hx.1))),
        Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr hx.1)), hx.2⟩)⟩⟩

omit [AddMonoid C] [Inhabited K] in
/-- What a slot modifies lies in the footprint of the slots of its level. -/
theorem modifies_eighSlotsFp_of_slot {F' : Type*} {H : EighArenas} (hnd : H.handles.Nodup)
    {n d lo k t : ℕ}
    {s : EighStep F' k} {S S' : Store P K} (hk1 : 1 ≤ k) (hk : lo + k ≤ n)
    (hs : ∀ kp h Qp Qm Ap Am σ, s = .split kp h Qp Qm Ap Am σ → 0 < kp ∧ kp < k)
    (hm : Modifies (eighSlotFp H n d lo k s ++ [(t, 4, 1)]) S S') :
    Modifies (eighSlotsFp H n d t) S S' := by
  refine hm.of_cells fun b i hb x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · refine blockDisjoint_eighSlotFp s hk1 hk hs ?_ x hx
    intro hW
    rcases levelCell_of_win hk1 hk hW with ⟨hrec, hLC⟩ | hLC
    · exact ((blockDisjoint_eighRecordBlocks_iff hnd).mp fun y hy => hb y (by
        simp [eighSlotsFp, hy])) ⟨hrec, hLC⟩
    · exact (blockDisjoint_eighLevelBlocks_iff.mp fun y hy => hb y (by
        simp [eighSlotsFp, hy])) hLC
  · rw [List.mem_singleton] at hx
    subst hx
    exact hb _ (by simp [eighSlotsFp])

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A literal $q \ne 0$ decodes to a nonzero value when the roundoff is below $1$. -/
theorem dec_ne_zero_of_lit {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop} {p : P}
    (hsem : IsRelErrSem u dec safe I.sem) (hu : u p < 1) {q : ℕ} (hq : 1 ≤ q) {z : K}
    (hz : I.sem.lit p (q : ℚ) = some z) : dec p z ≠ 0 := by
  obtain ⟨δ, hδ, hd⟩ := hsem.lit_err p _ z hz
  have h1 : 0 < 1 + δ := by
    have := (abs_le.mp hδ).1
    linarith
  rw [hd]
  have : (0 : ℝ) < q := by exact_mod_cast hq
  push_cast
  positivity

omit [AddMonoid C] [Inhabited K] [DecidableEq P] in
/-- A split of a node step is proper, for every split index. -/
theorem eighStep_split_proper {M : FloatMachine K ℕ ℕ} {N F : ℕ} {R₀ β R ε : K} {ℓ k : ℕ}
    {A : Matrix (Fin k) (Fin k) (K × K)} {s : EighSample ℕ ℕ N} :
    ∀ kp h Qp Qm Ap Am σ, eighStep M N F R₀ β A R ε ℓ s = .split kp h Qp Qm Ap Am σ →
      0 < kp ∧ kp < k := fun _ _ _ _ _ _ _ => lt_of_eighStep_split

/-- The invariant of the slot loop of `NLAlib.eighDownLevel` after the slots below `w`, from the
state `s₀` before the loop: the shape and the tape positions are kept, the slots below `w` that
start a node of depth $d$ are done (`NLAlib.EighSlotDone`), and every cell outside their windows but
the cell $4$ of the scratch buffer `tH` keeps its value. -/
def DownSlotsInv (I : Interp P ι K C) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K))
    (p : P) (H : EighArenas) (n F ℓ₀ d tH : ℕ) (R₀ β ε : K) (A : Matrix (Fin n) (Fin n) (K × K))
    (s₀ s : St P K C) (w : ℕ) : Prop :=
  s.store.shape = s₀.store.shape ∧ s.pos = s₀.pos ∧
    (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
      EighSlotDone H I.sem s.store p (eighTapeMachine I p mmR qrR) n F d R₀ β lo y) ∧
    ∀ q b i, (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
        ¬ EighSlotWindow H n d lo y.k (EighChildSlot (eighStep (eighTapeMachine I p mmR qrR) n F R₀
            β
          y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i) →
      ¬ (b = tH ∧ i = 4) → s.store.read q b i = s₀.store.read q b i

/-- The last four instructions of the head of the level, then `rest`. -/
def eighDownHeadRest (p : P) (d : IExp ℕ) (Lv t : ℕ) (one : Cell ℕ ℕ)
    (rest : Builder P ι ℕ ℕ Unit) : Builder P ι ℕ ℕ Unit := do
  ins (.bin p .mul ⟨Lv, 2 * (d + 1)⟩ ⟨t, 3⟩ ⟨Lv, 2 * d⟩)
  ins (.bin p .div ⟨t, 1⟩ one ⟨t, 0⟩)
  ins (.bin p .sub ⟨t, 3⟩ one ⟨t, 1⟩)
  ins (.bin p .mul ⟨Lv, 2 * (d + 1) + 1⟩ ⟨t, 3⟩ ⟨Lv, 2 * d + 1⟩)
  rest

/-- The seven instructions that start the level of depth $d$, then `rest`: the next window and
tolerance, from the depth counter $\ell_0 + d$, into the cells $2(d + 1)$ and $2(d + 1) + 1$ of
`Lv`. -/
def eighDownHead (p : P) (L d : IExp ℕ) (Lv t : ℕ) (one two half : Cell ℕ ℕ)
    (rest : Builder P ι ℕ ℕ Unit) : Builder P ι ℕ ℕ Unit := do
  ins (.litIdx p ⟨t, 0⟩ (L + d))
  ins (.bin p .div ⟨t, 2⟩ two ⟨t, 0⟩)
  ins (.bin p .add ⟨t, 3⟩ half ⟨t, 2⟩)
  eighDownHeadRest p d Lv t one rest

/-- The operations the head of the level performs succeed: the literal $\ell_0 + d$ decodes to a
nonzero value, and the arithmetic is defined (the divisor nonzero). -/
def EighHeadOk (I : Interp P ι K C) (dec : P → K → ℝ) (p : P) (ℓ₀ d : ℕ) : Prop :=
  (∃ L, I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ) = some L ∧ dec p L ≠ 0) ∧
    (∀ x y : K, ∃ v, I.sem.bin p .add x y = some v) ∧
    (∀ x y : K, ∃ v, I.sem.bin p .mul x y = some v) ∧
    (∀ x y : K, ∃ v, I.sem.bin p .sub x y = some v) ∧
    (∀ x y : K, dec p y ≠ 0 → ∃ v, I.sem.bin p .div x y = some v)

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The standard model with $\ell_0 \ge 1$ gives `NLAlib.EighHeadOk`. -/
theorem eighHeadOk_of_sem {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop} {p : P}
    {ℓ₀ d : ℕ} (hs : IsRelErrSem u dec safe I.sem) (hsafe : ∀ p x, safe p x) (hu : u p < 1)
    (hℓ : 1 ≤ ℓ₀) : EighHeadOk I dec p ℓ₀ d :=
  ⟨⟨_, (hs.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) (hsafe p _)).choose_spec,
    dec_ne_zero_of_lit hs hu (by omega) (hs.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) (hsafe p _)).choose_spec⟩,
    fun x y => hs.bin_ok p .add x y trivial (fun h => by cases h) (hsafe p _),
    fun x y => hs.bin_ok p .mul x y trivial (fun h => by cases h) (hsafe p _),
    fun x y => hs.bin_ok p .sub x y trivial (fun h => by cases h) (hsafe p _),
    fun x y hy => hs.bin_ok p .div x y trivial (fun _ => hy) (hsafe p _)⟩

/-- Writing one cell leaves cells of other buffers alone. -/
theorem blockDisjoint_cell_buf_ne {b t i j : ℕ} (hb : b ≠ t) :
    ∀ x ∈ [(t, j, 1)], blockDisjoint (b, i, 1) x = true := fun x hx => by
  rw [List.mem_singleton] at hx
  subst hx
  exact blockDisjoint_of_fst_ne hb

/-- Writing one cell leaves another cell of the same buffer alone. -/
theorem blockDisjoint_cell_idx_ne {t i j : ℕ} (hij : i ≠ j) :
    ∀ x ∈ [(t, j, 1)], blockDisjoint (t, i, 1) x = true := fun x hx => by
  rw [List.mem_singleton] at hx
  subst hx
  rw [blockDisjoint_iff]
  dsimp only
  omega

/-- The last four instructions of the head, then a continuation: from the sum
$\mathrm{fl}(1/2) + \mathrm{fl}(2/\ell)$ in `t[3]`, $\ell$ in `t[0]`, the constant one, the window
and tolerance of depth $d$, the next window and tolerance are stored. No printed source. -/
theorem wp_eighDownHeadRest (md : Mode) {dec : P → K → ℝ} (p : P) (ℓ₀ d D : ℕ)
    (H : EighArenas) {c t : ℕ} {R ε T3 : K} (hct : c ≠ t) (hLt : H.Lv ≠ t) (hcL : c ≠ H.Lv)
    (hOk : md.Needs (EighHeadOk I dec p ℓ₀ d ∧ d < D)) (rest : Builder P ι ℕ ℕ Unit)
    {Q : St P K C → Prop} {st : St P K C}
    (hpre : st.store.shape[t]? = some (p, 5) ∧ st.store.shape[H.Lv]? = some (p, 2 * (D + 1)) ∧
      st.store.read p t 3 = some T3 ∧
      st.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d)) ∧
      st.store.read p c 0 = some (eighTapeMachine I p mmR qrR).one ∧
      st.store.read p H.Lv (2 * d) = some R ∧ st.store.read p H.Lv (2 * d + 1) = some ε)
    (hk : ∀ st', Modifies [(t, 1, 3), (H.Lv, 2 * (d + 1), 2)] st.store st'.store →
      st'.store.read p H.Lv (2 * (d + 1)) = some ((eighTapeMachine I p mmR qrR).mul T3 R) →
      st'.store.read p H.Lv (2 * (d + 1) + 1) = some ((eighTapeMachine I p mmR qrR).mul
        ((eighTapeMachine I p mmR qrR).sub (eighTapeMachine I p mmR qrR).one
          ((eighTapeMachine I p mmR qrR).div (eighTapeMachine I p mmR qrR).one
            ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d)))) ε) → PosKept st st' →
      Wp md I rest.run Q st') :
    Wp md I (eighDownHeadRest p (.const d) H.Lv t ⟨c, 0⟩ rest).run Q st := by
  obtain ⟨hT, hLvs, r3, r0, c0, hR, hε⟩ := hpre
  unfold eighDownHeadRest
  set M := eighTapeMachine I p mmR qrR with hMdef
  have hWt : ∀ s : Store P K, s.shape[t]? = some (p, 5) → ∀ j < 5, Writable s p t j 1 :=
    fun s hs j hj i hi => ⟨5, hs, by omega⟩
  have hWL : ∀ s : Store P K, s.shape = st.store.shape → d < D → ∀ j < 2 * d + 4,
      Writable s p H.Lv j 1 := fun s hs hdD j hj i hi => ⟨_, by rw [hs]; exact hLvs, by omega⟩
  have hne1 : 2 * (d + 1) ≠ (2 * (IExp.const d + 1) + 1 : IExp ℕ).eval := by
    simp only [IExp.eval_mul, IExp.eval_ofNat, IExp.eval_add, IExp.eval_const]
    omega
  have hne2 : 2 * d + 1 ≠ (2 * (IExp.const d + 1) : IExp ℕ).eval := by
    simp only [IExp.eval_mul, IExp.eval_ofNat, IExp.eval_add, IExp.eval_const]
    omega
  -- the next window
  refine (RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .mul)
    (dst := ⟨H.Lv, 2 * (IExp.const d + 1)⟩) (x := ⟨t, 3⟩) (y := ⟨H.Lv, 2 * IExp.const d⟩)
    (a := T3) (b := R))).wp_bind (st := st) ⟨r3, by simpa using hR, hOk.mono fun h =>
      ⟨h.1.2.2.1 _ _, by simpa using hWL _ rfl h.2 (2 * (d + 1)) (by omega)⟩⟩
    fun st₁ hm₁ h₁ => ?_
  have sh1 : st₁.store.shape[t]? = some (p, 5) := by rw [hm₁.1]; exact hT
  have rV1 : st₁.store.read p H.Lv (2 * (d + 1)) = some (M.mul T3 R) := h₁.1
  -- 1 / (ℓ₀ + d)
  refine (RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .div)
    (dst := ⟨t, 1⟩) (x := ⟨c, 0⟩) (y := ⟨t, 0⟩) (a := M.one) (b := M.ofNat (ℓ₀ + d)))).wp_bind
    (st := st₁) ⟨(hm₁.2 p c 0 (blockDisjoint_cell_buf_ne hcL)).trans c0,
      (hm₁.2 p t 0 (blockDisjoint_cell_buf_ne hLt.symm)).trans r0,
      hOk.mono fun ⟨⟨⟨L', hL', hLne⟩, _, _, _, hdiv⟩, _⟩ =>
        ⟨hdiv _ _ (by change dec p ((I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD default) ≠ 0
                      rw [hL', Option.getD_some]; exact hLne), hWt _ sh1 1 (by omega)⟩⟩
    fun st₂ hm₂ h₂ => ?_
  have sh2 : st₂.store.shape[t]? = some (p, 5) := by rw [hm₂.1]; exact sh1
  have r2 : st₂.store.read p t 1 = some (M.div M.one (M.ofNat (ℓ₀ + d))) := h₂.1
  -- 1 - 1 / (ℓ₀ + d)
  refine (RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .sub)
    (dst := ⟨t, 3⟩) (x := ⟨c, 0⟩) (y := ⟨t, 1⟩) (a := M.one)
    (b := M.div M.one (M.ofNat (ℓ₀ + d))))).wp_bind (st := st₂)
    ⟨(hm₂.2 p c 0 (blockDisjoint_cell_buf_ne hct)).trans ((hm₁.2 p c 0
      (blockDisjoint_cell_buf_ne hcL)).trans c0), r2,
      hOk.mono fun ⟨⟨_, _, _, hsub, _⟩, _⟩ => ⟨hsub _ _, hWt _ sh2 3 (by omega)⟩⟩
    fun st₃ hm₃ h₃ => ?_
  have r3' : st₃.store.read p t 3 = some (M.sub M.one (M.div M.one (M.ofNat (ℓ₀ + d)))) := h₃.1
  have rε3 : st₃.store.read p H.Lv (2 * d + 1) = some ε :=
    (hm₃.2 p _ _ (blockDisjoint_cell_buf_ne hLt)).trans ((hm₂.2 p _ _
      (blockDisjoint_cell_buf_ne hLt)).trans ((hm₁.2 p _ _ (blockDisjoint_cell_idx_ne
        hne2)).trans hε))
  -- the next tolerance
  refine (RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .mul)
    (dst := ⟨H.Lv, 2 * (IExp.const d + 1) + 1⟩) (x := ⟨t, 3⟩) (y := ⟨H.Lv, 2 * IExp.const d + 1⟩)
    (a := M.sub M.one (M.div M.one (M.ofNat (ℓ₀ + d)))) (b := ε))).wp_bind (st := st₃)
    ⟨r3', by simpa using rε3, hOk.mono fun h => ⟨h.1.2.2.1 _ _, by
      simpa using hWL _ (hm₃.1.trans (hm₂.1.trans hm₁.1)) h.2 (2 * (d + 1) + 1) (by omega)⟩⟩
    fun st₄ hm₄ h₄ => ?_
  have hsub : ∀ x ∈ [(H.Lv, (2 * (IExp.const d + 1) : IExp ℕ).eval, 1)] ++ [(t, 1, 1)] ++
      [(t, 3, 1)] ++ [(H.Lv, (2 * (IExp.const d + 1) + 1 : IExp ℕ).eval, 1)],
      ∃ y ∈ [(t, 1, 3), (H.Lv, 2 * (d + 1), 2)],
        x.1 = y.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.1 + x.2.2 ≤ y.2.1 + y.2.2 := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with ((rfl | rfl) | rfl) | rfl <;>
      first
        | exact ⟨(t, 1, 3), by simp, rfl, by simp, by simp⟩
        | exact ⟨(H.Lv, 2 * (d + 1), 2), by simp, rfl, by simp, by simp⟩
  have hmod := (hm₁.trans hm₂).trans hm₃
  have hmod := hmod.trans hm₄
  refine hk st₄ (hmod.of_sub hsub) ?_ h₄.1 ?_
  · exact (hm₄.2 p _ _ (blockDisjoint_cell_idx_ne hne1)).trans ((hm₃.2 p _ _
      (blockDisjoint_cell_buf_ne hLt)).trans ((hm₂.2 p _ _
        (blockDisjoint_cell_buf_ne hLt)).trans rV1))
  · exact h₄.2.trans (h₃.2.trans (h₂.2.trans h₁.2))

/-- The first instructions of the level, then a continuation: with the constants stored, the
window and tolerance of depth $d$ in the cells $2d$, $2d + 1$ of `Lv` and the scratch buffer `t`
of $5$ cells, the next window and tolerance (`NLAlib.eighNextParams`) are stored in the cells
$2(d + 1)$ and $2(d + 1) + 1$, and only these and the cells $0$ to $3$ of `t` change; the
continuation then starts from any such state. In mode `total` the instructions succeed, given the
standard model, $\ell_0 \ge 1$ and $d < D$. No printed source. -/
theorem wp_eighDownHead (md : Mode) {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (p : P) (n ℓ₀ d D : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (H : EighArenas) {c t : ℕ} {R ε : K} (hct : c ≠ t) (hLt : H.Lv ≠ t)
    (hcL : c ≠ H.Lv) (hlit1 : ∃ z, I.sem.lit p 1 = some z)
    (hlit2 : ∃ z, I.sem.lit p ((2 : ℕ) : ℚ) = some z) (rest : Builder P ι ℕ ℕ Unit)
    {Q : St P K C → Prop} {st : St P K C}
    (hpre : H.Shaped st.store p n D ∧ st.store.shape[t]? = some (p, 5) ∧
        st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
        st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
          (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
        st.store.read p H.Lv (2 * d) = some R ∧ st.store.read p H.Lv (2 * d + 1) = some ε ∧
        md.Needs (1 ≤ ℓ₀ ∧ d < D))
    (hk : ∀ st', Modifies [(t, 0, 4), (H.Lv, 2 * (d + 1), 2)] st.store st'.store →
      st'.store.read p H.Lv (2 * (d + 1)) =
        some (eighNextParams (eighTapeMachine I p mmR qrR) R ε (ℓ₀ + d)).1 →
      st'.store.read p H.Lv (2 * (d + 1) + 1) =
        some (eighNextParams (eighTapeMachine I p mmR qrR) R ε (ℓ₀ + d)).2 → PosKept st st' →
      Wp md I rest.run Q st') :
    Wp md I (eighDownHead p (.const ℓ₀) (.const d) H.Lv t ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ rest).run Q st := by
  obtain ⟨z₂, hz₂⟩ := hlit2
  obtain ⟨o, ho⟩ := hlit1
  have hM1 : (eighTapeMachine I p mmR qrR).one = o := by
    change (I.sem.lit p 1).getD default = o
    rw [ho, Option.getD_some]
  have hM2 : (eighTapeMachine I p mmR qrR).ofNat 2 = z₂ := by
    change (I.sem.lit p ((2 : ℕ) : ℚ)).getD default = z₂
    rw [hz₂, Option.getD_some]
  obtain ⟨hH, hT, c0, c1, c2, hR, hε, hN⟩ := hpre
  unfold eighDownHead
  obtain ⟨-, -, -, -, -, -, -, -, hLvs⟩ := hH
  have hOk : md.Needs (EighHeadOk I dec p ℓ₀ d ∧ d < D) :=
    (Mode.needs_and.mpr ⟨hsem, hN⟩).mono fun ⟨⟨hs, hsafe, hu⟩, hℓ, hdD⟩ =>
      ⟨eighHeadOk_of_sem hs hsafe hu hℓ, hdD⟩
  have hWt : ∀ s : Store P K, s.shape[t]? = some (p, 5) → ∀ j < 5, Writable s p t j 1 :=
    fun s hs j hj i hi => ⟨5, hs, by omega⟩
  set M := eighTapeMachine I p mmR qrR with hMdef
  have c0' : st.store.read p c 0 = some M.one := c0.trans (ho.trans (congrArg some hM1.symm))
  have c1' : st.store.read p c 1 = some (M.ofNat 2) :=
    c1.trans (hz₂.trans (congrArg some hM2.symm))
  -- the depth counter
  refine (RoutineSpec.ins (spec_litIdx_getD (m := md) (I := I) (p := p) (dst := ⟨t, 0⟩)
    (e := IExp.const ℓ₀ + IExp.const d))).wp_bind (st := st)
    (hOk.mono fun ⟨⟨⟨L', hL', _⟩, _⟩, _⟩ => ⟨⟨L', by simpa using hL'⟩,
      hWt _ hT 0 (by omega)⟩) fun st₁ hm₁ h₁ => ?_
  have sh1 : st₁.store.shape[t]? = some (p, 5) := by rw [hm₁.1]; exact hT
  have r1 : st₁.store.read p t 0 = some (M.ofNat (ℓ₀ + d)) := h₁.1
  -- 2 / (ℓ₀ + d)
  refine (RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .div)
    (dst := ⟨t, 2⟩) (x := ⟨c, 1⟩) (y := ⟨t, 0⟩) (a := M.ofNat 2) (b := M.ofNat (ℓ₀ + d)))).wp_bind
    (st := st₁) ⟨(hm₁.2 p c 1 (blockDisjoint_cell_buf_ne hct)).trans c1', r1,
      hOk.mono fun ⟨⟨⟨L', hL', hLne⟩, _, _, _, hdiv⟩, _⟩ =>
        ⟨hdiv _ _ (by change dec p ((I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD default) ≠ 0
                      rw [hL', Option.getD_some]; exact hLne), hWt _ sh1 2 (by omega)⟩⟩
    fun st₂ hm₂ h₂ => ?_
  have sh2 : st₂.store.shape[t]? = some (p, 5) := by rw [hm₂.1]; exact sh1
  have r2 : st₂.store.read p t 2 = some (M.div (M.ofNat 2) (M.ofNat (ℓ₀ + d))) := h₂.1
  -- 1 / 2 + 2 / (ℓ₀ + d)
  refine (RoutineSpec.ins (spec_bin_getD (m := md) (I := I) (p := p) (op := .add)
    (dst := ⟨t, 3⟩) (x := ⟨c, 2⟩) (y := ⟨t, 2⟩) (a := M.div M.one (M.ofNat 2))
    (b := M.div (M.ofNat 2) (M.ofNat (ℓ₀ + d))))).wp_bind (st := st₂)
    ⟨(hm₂.2 p c 2 (blockDisjoint_cell_buf_ne hct)).trans ((hm₁.2 p c 2
      (blockDisjoint_cell_buf_ne hct)).trans c2), r2,
      hOk.mono fun ⟨⟨_, hadd, _⟩, _⟩ => ⟨hadd _ _, hWt _ sh2 3 (by omega)⟩⟩
    fun st₃ hm₃ h₃ => ?_
  have sh3 : st₃.store.shape[t]? = some (p, 5) := by rw [hm₃.1]; exact sh2
  refine wp_eighDownHeadRest (mmR := mmR) (qrR := qrR) (R := R) (ε := ε)
    (T3 := M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat (ℓ₀ + d)))) md p ℓ₀ d D H
    hct hLt hcL hOk rest ?_ ?_
  · refine ⟨sh3, by rw [hm₃.1, hm₂.1, hm₁.1]; exact hLvs, h₃.1, ?_, ?_, ?_, ?_⟩
    · exact (hm₃.2 p t 0 (blockDisjoint_cell_idx_ne (j := 3) (by omega))).trans
        ((hm₂.2 p t 0 (blockDisjoint_cell_idx_ne (j := 2) (by omega))).trans r1)
    · exact (hm₃.2 p c 0 (blockDisjoint_cell_buf_ne hct)).trans ((hm₂.2 p c 0
        (blockDisjoint_cell_buf_ne hct)).trans ((hm₁.2 p c 0 (blockDisjoint_cell_buf_ne hct)).trans
          c0'))
    · exact (hm₃.2 p _ _ (blockDisjoint_cell_buf_ne hLt)).trans ((hm₂.2 p _ _
        (blockDisjoint_cell_buf_ne hLt)).trans ((hm₁.2 p _ _ (blockDisjoint_cell_buf_ne hLt)).trans
          hR))
    · exact (hm₃.2 p _ _ (blockDisjoint_cell_buf_ne hLt)).trans ((hm₂.2 p _ _
        (blockDisjoint_cell_buf_ne hLt)).trans ((hm₁.2 p _ _ (blockDisjoint_cell_buf_ne hLt)).trans
          hε))
  · intro st₄ hm₄ rV1 rV2 hp4
    have hsub : ∀ x ∈ ([(t, 0, 1)] ++ [(t, 2, 1)] ++ [(t, 3, 1)]) ++ [(t, 1, 3),
        (H.Lv, 2 * (d + 1), 2)], ∃ y ∈ [(t, 0, 4), (H.Lv, 2 * (d + 1), 2)],
        x.1 = y.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.1 + x.2.2 ≤ y.2.1 + y.2.2 := by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with ((rfl | rfl) | rfl) | rfl | rfl <;>
        first
          | exact ⟨(t, 0, 4), by simp, rfl, by simp, by simp⟩
          | exact ⟨(H.Lv, 2 * (d + 1), 2), by simp, rfl, by simp, by simp⟩
    refine hk st₄ ((((hm₁.trans hm₂).trans hm₃).trans hm₄).of_sub hsub) rV1 rV2 ?_
    exact hp4.trans (h₃.2.trans (h₂.2.trans h₁.2))

omit [AddMonoid C] in
/-- A slot that starts a node keeps the invariant `DownSlotsInv`: from the slot's own effect
(the slot is done, and every cell outside its window and `t[4]` is kept). -/
private theorem downSlotsInv_succ_of_slot {p : P} {H : EighArenas} {n F ℓ₀ d t w : ℕ}
    {s₀ s₁ s₂ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {a : List Bool}
    {y : EighNode K} (hlt : ∀ x ∈ H.handles, x < t) (hnd : H.handles.Nodup) (hn1 : 1 ≤ n)
    (ha : a.length = d)
    (hl : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y))
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A s₀ s₁ w)
    (hdone : EighSlotDone H I.sem s₂.store p (eighTapeMachine I p mmR qrR) n F d R₀ β w y)
    (hfrW : ∀ q b i, ¬ EighSlotWindow H n d w y.k (EighChildSlot (eighStep
      (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d w)) w) b i →
      ¬ (b = t ∧ i = 4) → s₂.store.read q b i = s₁.store.read q b i)
    (hsh2 : s₂.store.shape = s₁.store.shape) (hps2 : s₂.pos = s₁.pos) :
    DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A s₀ s₂ (w + 1) := by
  obtain ⟨hsh1, hps1, hdn1, hfr1⟩ := hinv
  refine ⟨hsh2.trans hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_, fun q b i hall ht4 => ?_⟩
  · obtain ⟨a', ha', hl'⟩ := hn'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
    · obtain ⟨hk1', hkn'⟩ := eighLoc_bounds hn1 hl'
      have hdis : lo + y'.k ≤ w := by
        have hae : a' ≠ a := by
          rintro rfl
          rw [hl] at hl'
          have := (Prod.mk.inj (Option.some_inj.mp hl')).1
          omega
        rcases eighLoc_disjoint (ha'.trans ha.symm) hae hl' hl with h | h <;> omega
      exact EighSlotDone.of_read_eq hk1' hkn' (fun b i hwin => hfrW p b i
        (fun hw' => false_of_eighSlotWindow_of_eighSlotWindow hnd hk1' hdis hwin hw')
        (fun h => by
          have := lt_of_win hlt hwin
          omega)) (hdn1 lo y' hlo ⟨a', ha', hl'⟩)
    · obtain rfl : y = y' := eq_of_eighLoc_slot hn1 (ha.trans ha'.symm) hl hl'
      exact hdone
  · rw [hfrW q b i (hall w y (Nat.lt_succ_self w) ⟨a, ha, hl⟩) ht4]
    exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4

omit [AddMonoid C] in
/-- A slot that starts no node changes nothing, and keeps the invariant `DownSlotsInv`. -/
private theorem downSlotsInv_succ_skip {p : P} {H : EighArenas} {n F ℓ₀ d t w : ℕ}
    {s₀ s₁ s₂ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hno : ¬ ∃ (y : EighNode K) (a : List Bool), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y))
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A s₀ s₁ w) (hst : s₂.store = s₁.store)
    (hps : s₂.pos = s₁.pos) : DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A s₀ s₂ (w + 1) := by
  obtain ⟨hsh1, hps1, hdn1, hfr1⟩ := hinv
  refine ⟨by rw [hst]; exact hsh1, hps.trans hps1, fun lo y' hlo hn' => ?_,
    fun q b i hall ht4 => ?_⟩ <;> rw [hst]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
    · exact hdn1 lo y' hlo hn'
    · obtain ⟨a', ha', hl'⟩ := hn'
      exact absurd ⟨y', a', ha', hl'⟩ hno
  · exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- An arithmetic operation of the standard model succeeds, with its rounding. -/
theorem exists_bin_eq_some {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) {b : BinOp} (hb : b.IsArith)
    {x y : K} (hy : b = .div → dec p y ≠ 0) :
    ∃ z, I.sem.bin p b x y = some z ∧
      ∃ δ : ℝ, |δ| ≤ u p ∧ dec p z = b.realOp (dec p x) (dec p y) * (1 + δ) := by
  obtain ⟨z, hz⟩ := hsem.bin_ok p b x y hb hy trivial
  exact ⟨z, hz, hsem.bin_err p b x y z hb hz⟩

omit [DecidableEq P] [AddMonoid C] in
/-- The windows of the levels decode to positive values from a positive $R_0$ and to $0$
from a zero $R_0$. -/
theorem eighLevelParams_fst_pos_zero {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (hsem : IsRelErrSem u dec safe I.sem) (hsafe : ∀ p x, safe p x) (p : P) (hu : u p < 1)
    (hlit : IsExactIntLit dec I.sem 2) {R₀ ε : K} {ℓ₀ : ℕ} (hℓ : 1 ≤ ℓ₀) :
    ∀ d, (0 < dec p R₀ → 0 < dec p (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1) ∧
      (dec p R₀ = 0 → dec p (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1 = 0) := by
  have hsem : IsRelErrSem u dec (fun _ _ => True) I.sem :=
    hsem.mono_safe (fun p x _ => hsafe p x)
  classical
  have hpos : ∀ {δ : ℝ}, |δ| ≤ u p → 0 < 1 + δ := fun h => by
    have := (abs_le.mp h).1; linarith
  obtain ⟨one, hone, hone'⟩ := hlit p 1 (by omega)
  obtain ⟨two, htwo, htwo'⟩ := hlit p 2 (by omega)
  simp only [Nat.cast_one] at hone hone'
  push_cast at htwo'
  intro d
  induction d with
  | zero => exact ⟨id, id⟩
  | succ d ih =>
    obtain ⟨L, hL⟩ := hsem.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) trivial
    obtain ⟨δL, hδL, hLd⟩ := hsem.lit_err p _ L hL
    have hLpos : 0 < dec p L := by
      rw [hLd]
      have hx : (0 : ℝ) < (((ℓ₀ + d : ℕ) : ℚ) : ℝ) := by
        exact_mod_cast (show 0 < ℓ₀ + d by omega)
      exact mul_pos hx (hpos hδL)
    obtain ⟨h1, hh1, δ1, hδ1, hd1⟩ := exists_bin_eq_some hsem p (b := .div) trivial (x := one) (y :=
        two)
      (fun _ => by rw [htwo']; norm_num)
    obtain ⟨h2, hh2, δ2, hδ2, hd2⟩ := exists_bin_eq_some hsem p (b := .div) trivial (x := two) (y :=
        L)
      (fun _ => ne_of_gt hLpos)
    obtain ⟨h3, hh3, δ3, hδ3, hd3⟩ := exists_bin_eq_some hsem p (b := .add) trivial (x := h1) (y :=
        h2)
      (fun h => by cases h)
    obtain ⟨h4, hh4, δ4, hδ4, hd4⟩ := exists_bin_eq_some hsem p (b := .mul) trivial (x := h3)
      (y := (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1) (fun h => by cases h)
    have e : (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).1 = h4 := by
      change (I.sem.bin p .mul ((I.sem.bin p .add ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default) ((I.sem.bin p .div
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default) ((I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD
        default)).getD default)).getD default) _).getD default = h4
      rw [hone, htwo, hL]
      simp only [Option.getD_some]
      rw [hh1, Option.getD_some, hh2, Option.getD_some, hh3, Option.getD_some, hh4,
        Option.getD_some]
    have hX : 0 < dec p h3 := by
      simp only [BinOp.realOp] at hd1 hd2 hd3
      rw [hd3, hd1, hd2, hone', htwo']
      have := hpos hδ1; have := hpos hδ2; have := hpos hδ3
      have : 0 < 2 / dec p L := by positivity
      positivity
    simp only [BinOp.realOp] at hd4
    rw [e, hd4]
    have := hpos hδ4
    exact ⟨fun h => by have := ih.1 h; positivity, fun h => by rw [ih.2 h]; ring⟩

/-- The precondition of the slot loop of `NLAlib.eighDownLevel` at depth $d$: the scratch buffer
`t` of $5$ cells is the last buffer, the arenas hold the nodes of depth $d$, the parameters, the
constants and the draws of the level are stored, and in mode `total` $R_0 \ge 0$, $\ell_0 \ge 1$
and $d < D$. -/
def EighDownPre (I : Interp P ι K C) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K))
    (md : Mode) (dec : P → K → ℝ) (p : P) (H : EighArenas) (n F ℓ₀ d D par Su Sg c t : ℕ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (R₀ ε β : K) (st : St P K C) : Prop :=
  st.store.size = t + 1 ∧ H.Shaped st.store p n D ∧ st.store.shape[t]? = some (p, 5) ∧
    H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
    (st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β) ∧
    (st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p)) ∧
    (∀ w < n, st.store.read p Su w = some (I.tape .uniform (n * d + w))) ∧
    (∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) ∧
    (Su = t → n ≤ 5) ∧ (Sg = t → 4 * (n * n) ≤ 5) ∧ md.Needs (0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀ ∧ d < D)

omit [AddMonoid C] in
/-- The plain inputs of the slot of a node of depth $d$ are stored, when the arenas hold the nodes
of depth $d$ and the level's parameters, constants and draws are stored. -/
theorem eighSlotIn_of_downPre {p : P} {H : EighArenas} {n F ℓ₀ d lo par Su Sg c : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {s : Store P K} {a : List Bool}
    {y : EighNode K} (hn1 : 1 ≤ n) (ha : a.length = d)
    (hl : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (hlev : H.LevelHolds I.sem s p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : s.read p par 0 = some R₀ ∧ s.read p par 2 = some β)
    (hc : s.read p c 0 = I.sem.lit p 1 ∧ s.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      s.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      s.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      s.read p c 4 = some (I.sem.sqrtHalf p))
    (hSu : ∀ w < n, s.read p Su w = some (I.tape .uniform (n * d + w)))
    (hSg : ∀ w < 4 * (n * n), s.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) :
    EighSlotIn I mmR qrR p H n d lo par Su Sg c R₀ β y s := by
  obtain ⟨hyR, hyε, -⟩ := eighLoc_params hl
  rw [ha] at hyR hyε
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn1 hl
  exact ⟨(hlev.1 a lo y ha hl).2, hlev.2.2.1.trans (congrArg some hyR.symm),
    hlev.2.2.2.trans (congrArg some hyε.symm), hpar.1, hpar.2,
    fun _ => ⟨hSu lo (by omega), hSg⟩, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩

omit [AddMonoid C] in
/-- A cell of the parameters, constants, samples or window cells, or of the size and node arenas
below depth $d + 1$, other than `t[4]`, keeps its value through the slots before `lo`. -/
private theorem downSlotsInv_read_eq {p : P} {H : EighArenas} {n F ℓ₀ d t par Su Sg c lo : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {s₀ s : St P K C}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A s₀ s lo) (q : P) (b i : ℕ)
    (h4 : ¬ (b = t ∧ i = 4))
    (hb : ((b = par ∨ b = Su ∨ b = Sg ∨ b = c ∨ b = H.Lv) ∨ (b = H.Sz ∧ i < n * (d + 1)) ∨
      (b = H.Ma ∧ i < 2 * (n * n) * (d + 1)))) : s.store.read q b i = s₀.store.read q b i := by
  have hnd : H.handles.Nodup := hbufs.sublist (List.sublist_append_left _ _)
  refine hinv.2.2.2 q b i (fun lo' y' _ _ => ?_) h4
  rcases hb with hb | ⟨rfl, hi⟩ | ⟨rfl, hi⟩
  · exact not_eighSlotWindow_of_not_mem (not_mem_slotBufs hbufs hb)
  · exact not_eighSlotWindow_sz hnd hi
  · exact not_eighSlotWindow_ma hnd hi

/-- The slot of a node in the loop of `NLAlib.eighDownLevel` keeps the invariant `DownSlotsInv`,
and modifies only the footprint of the slots of the level. -/
theorem spec_eighDownSlot_node {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n F ℓ₀ d D : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c t : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (ht : t ∉ H.handles ++ [par, c])
    (hlt : ∀ x ∈ H.handles ++ [par, c], x < t) {st₀ : St P K C}
    (hpre : EighDownPre I mmR qrR md dec p H n F ℓ₀ d D par Su Sg c t A R₀ ε β st₀) {lo : ℕ}
    (hlo : lo < n) {y : EighNode K} {a : List Bool} (ha : a.length = d)
    (hl : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) :
    Spec md I (fun st => DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A st₀ st lo)
      (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo).run
      (eighSlotsFp H n d t) fun _ st' => DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A st₀ st'
        (lo + 1) := by
  obtain ⟨hsz0, hH0, hT0, hlev, hpar, hc, hSu, hSg, hSut5, hSgt5, hN⟩ := hpre
  intro st hinv
  have hnd : H.handles.Nodup := hbufs.sublist (List.sublist_append_left _ _)
  have hlt' : ∀ x ∈ H.handles, x < t := fun x hx => hlt x (List.mem_append_left _ hx)
  have hlpc : par < t ∧ c < t := ⟨hlt _ (by simp), hlt _ (by simp)⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hsh1, hps1, hdn1, hfr1⟩ := hinv
  have hbt : ∀ x, (x = par ∨ x = c ∨ x = H.Lv) → x ≠ t := fun x hx h =>
    ht (by
      rw [← h]
      rcases hx with hx | hx | hx <;> simp [hx, EighArenas.handles])
  have hSzt : H.Sz ≠ t := fun h => lt_irrefl _ (h ▸ hlt' H.Sz (by simp [EighArenas.handles]))
  have hMat : H.Ma ≠ t := fun h => lt_irrefl _ (h ▸ hlt' H.Ma (by simp [EighArenas.handles]))
  have hnW : ∀ q b i, ¬ (b = t ∧ i = 4) → ((b = par ∨ b = Su ∨ b = Sg ∨ b = c ∨ b = H.Lv) ∨
      (b = H.Sz ∧ i < n * (d + 1)) ∨ (b = H.Ma ∧ i < 2 * (n * n) * (d + 1))) →
      st.store.read q b i = st₀.store.read q b i := fun q b i h4 hb =>
    downSlotsInv_read_eq hbufs ⟨hsh1, hps1, hdn1, hfr1⟩ q b i h4 hb
  have hsz : st.store.size = t + 1 := (Store.size_eq_of_shape_eq hsh1).trans hsz0
  have hH : H.Shaped st.store p n D := EighArenas.Shaped.of_shape_eq (fun b _ => by rw [hsh1]) hH0
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn1 hl
  obtain ⟨hyR, hyε, hyℓ⟩ := eighLoc_params hl
  rw [ha] at hyR hyε hyℓ
  have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
  have e5 : 2 * n * lo + 2 * (y.k * y.k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) hkn
    nlinarith
  have e6 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have hSuT : 2 ≤ y.k → Su = t → lo ≠ 4 := fun hk h => by
    have := hSut5 h
    omega
  have hSgT : 2 ≤ y.k → Sg ≠ t := fun hk h => by
    have := hSgt5 h
    have : 2 * 2 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hIn := (eighSlotIn_of_downPre hn1 ha hl hlev hpar hc hSu hSg).of_read_eq
    fun q b i hb => by
      rcases hb with hb | hb | hb | ⟨hb, h1, h2⟩ | ⟨hk, ⟨hb, hi⟩ | ⟨hb, -⟩⟩
      · exact hnW q b i (fun h => hbt _ (Or.inr (Or.inr hb)) h.1) (Or.inl (Or.inr (Or.inr
          (Or.inr (Or.inr hb)))))
      · exact hnW q b i (fun h => hbt _ (Or.inl hb) h.1) (Or.inl (Or.inl hb))
      · exact hnW q b i (fun h => hbt _ (Or.inr (Or.inl hb)) h.1) (Or.inl (Or.inr (Or.inr
          (Or.inr (Or.inl hb)))))
      · exact hnW q b i (fun h => hMat (hb ▸ h.1)) (Or.inr (Or.inr ⟨hb, by omega⟩))
      · exact hnW q b i (fun h => hSuT hk (hb ▸ h.1) (hi ▸ h.2)) (Or.inl (Or.inr (Or.inl hb)))
      · exact hnW q b i (fun h => hSgT hk (hb ▸ h.1)) (Or.inl (Or.inr (Or.inr (Or.inl hb))))
  obtain ⟨v, hvr0, hv⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hl).1
  have hvr : st.store.read p H.Sz (n * d + lo) = some v :=
    (hnW p H.Sz _ (fun h => hSzt h.1)
      (Or.inr (Or.inl ⟨rfl, by rw [Nat.mul_succ]; omega⟩))).trans hvr0
  have hNd : md.Needs (Writable st.store p t 4 1 ∧ 0 ≤ dec p R₀ ∧
      (0 < dec p R₀ → 0 < dec p y.R) ∧ (dec p R₀ = 0 → dec p y.R = 0) ∧ 1 ≤ ℓ₀ + d ∧ d < D) :=
    (Mode.needs_and.mpr ⟨hsem, hN⟩).mono
    fun ⟨⟨hs, hsafe, hu⟩, hR0, hℓ1, hdD⟩ => ⟨fun i hi => ⟨5, by rw [hsh1]; exact hT0,
      by omega⟩, hR0, fun h => by
        rw [hyR]
        exact (eighLevelParams_fst_pos_zero hs hsafe p hu (fun q k hk => hlit q k (by omega))
          hℓ1 d).1 h, fun h => by
        rw [hyR]
        exact (eighLevelParams_fst_pos_zero hs hsafe p hu (fun q k hk => hlit q k (by omega))
          hℓ1 d).2 h, by omega, hdD⟩
  refine wp_mono ((spec_eighSlotBody hmm hqr md p n ℓ₀ F d D lo hsem hflag hcmp hlit htn H hk1
    hkn hyℓ hbufs ht hSuT hSgT (b := t + 1) (fun hk x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · have := hlt x (List.mem_append_left _ hx)
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact Nat.lt_of_lt_of_le hlpc.1 (Nat.le_succ _)
        · have := Store.lt_size_of_read_eq_some (hSu 0 (by omega))
          omega
        · have := Store.lt_size_of_read_eq_some (hSg 0 (by positivity))
          omega
        · exact Nat.lt_of_lt_of_le hlpc.2 (Nat.le_succ _)) v hv).spec st
    ⟨hvr, hsz, hH, hIn, hNd⟩)
    fun st' ⟨hm, hdone, hp⟩ => ⟨modifies_eighSlotsFp_of_slot hnd hk1 hkn eighStep_split_proper hm,
      downSlotsInv_succ_of_slot hlt' hnd hn1 ha hl ⟨hsh1, hps1, hdn1, hfr1⟩ hdone
        (fun q b i hW ht4 => read_eq_of_modifies_eighSlotFp _ hk1 hkn eighStep_split_proper hm hW
          ht4) hm.1
        hp⟩

/-- One slot of the loop of `NLAlib.eighDownLevel` keeps the invariant `DownSlotsInv`, and modifies
only the footprint of the slots of the level. -/
theorem spec_eighDownSlot_step {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n F ℓ₀ d D : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c t : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (ht : t ∉ H.handles ++ [par, c])
    (hlt : ∀ x ∈ H.handles ++ [par, c], x < t) {st₀ : St P K C}
    (hpre : EighDownPre I mmR qrR md dec p H n F ℓ₀ d D par Su Sg c t A R₀ ε β st₀) {lo : ℕ}
    (hlo : lo < n) :
    Spec md I (fun st => DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A st₀ st lo)
      (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo).run
      (eighSlotsFp H n d t) fun _ st' => DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A st₀ st'
        (lo + 1) := by
  by_cases hnode : ∃ (y : EighNode K) (a : List Bool), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
  · obtain ⟨y, a, ha, hl⟩ := hnode
    exact spec_eighDownSlot_node hmm hqr md p n F ℓ₀ d D hsem hflag hcmp hlit htn H hbufs ht hlt
      hpre hlo ha hl
  · obtain ⟨hsz0, hH0, hT0, hlev, hpar, hc, hSu, hSg, hSut5, hSgt5, hN⟩ := hpre
    intro st hinv
    have hSzt : ¬ (H.Sz = t ∧ n * d + lo = 4) := fun h => lt_irrefl _
      (h.1 ▸ hlt _ (List.mem_append_left _ (by simp [EighArenas.handles])))
    obtain ⟨v, hvr0, hv⟩ := Option.bind_eq_some_iff.mp
      (hlev.2.1 lo hlo fun a y ha hl => hnode ⟨y, a, ha, hl⟩)
    have hvr : st.store.read p H.Sz (n * d + lo) = some v :=
      (downSlotsInv_read_eq hbufs hinv p _ _ hSzt
        (Or.inr (Or.inl ⟨rfl, by rw [Nat.mul_succ]; omega⟩))).trans hvr0
    refine wp_mono ((spec_eighSlotBody_skip (mm := mm) (qr := qr) md p n ℓ₀ F d lo par H.Lv Su Sg
      H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t v hv).spec st hvr) fun st' ⟨hm, hst, hp⟩ =>
      ⟨hm.mono fun x hx => absurd hx List.not_mem_nil,
        downSlotsInv_succ_skip hnode hinv hst hp⟩

/-- The slot loop of `NLAlib.eighDownLevel` as a routine specification. -/
theorem spec_eighDownSlots {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n F ℓ₀ d D : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c t : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (ht : t ∉ H.handles ++ [par, c])
    (hlt : ∀ x ∈ H.handles ++ [par, c], x < t) :
    RoutineSpec md I (EighDownPre I mmR qrR md dec p H n F ℓ₀ d D par Su Sg c t A R₀ ε β)
      (Builder.forRange (.const n) fun lo =>
        eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo)
      (eighSlotsFp H n d t) fun st₀ st' =>
        DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A st₀ st' n :=
  RoutineSpec.forRange_const _ (fun st₀ w st => DownSlotsInv I mmR qrR p H n F ℓ₀ d t R₀ β ε A
    st₀ st w) (fun _ _ => ⟨rfl, rfl, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ _ _ => rfl⟩)
    fun _ hpre _ hlo => spec_eighDownSlot_step hmm hqr md p n F ℓ₀ d D hsem hflag hcmp hlit htn
      H hbufs ht hlt hpre hlo

omit [AddMonoid C] in
/-- After the slot loop, with the scratch buffer popped, the arenas hold the nodes of depth
$d + 1$: from the invariant `DownSlotsInv` at $n$, the size cells of depth $d + 1$ reading $0$
before the level, and the parameters of depth $d + 1$ stored before the loop. -/
private theorem levelHolds_succ_of_downSlots {p : P} {H : EighArenas} {n F ℓ₀ d tH : ℕ}
    {S : Store P K} {s₀ σ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hlt : ∀ x ∈ H.handles, x < tH) (hnd : H.handles.Nodup) (hsz : σ.store.size = tH + 1)
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A s₀ σ n)
    (hnext : ∀ lo < n, ReadsIdx I.sem S p H.Sz (n * (d + 1) + lo) 0)
    (hSz : ∀ j, s₀.store.read p H.Sz j = S.read p H.Sz j)
    (hW1 : s₀.store.read p H.Lv (2 * (d + 1)) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).1)
    (hW2 : s₀.store.read p H.Lv (2 * (d + 1) + 1) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).2) :
    H.LevelHolds I.sem (Array.pop σ.store) p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) := by
  obtain ⟨-, -, hdne, hfre⟩ := hinv
  have hpop : ∀ q b i, b < tH → Store.read (Array.pop σ.store) q b i = σ.store.read q b i :=
    fun q b i hb => Store.read_pop_of_lt (by omega)
  have hSzT : H.Sz < tH := hlt _ (by simp [EighArenas.handles])
  have hLvT : H.Lv < tH := hlt _ (by simp [EighArenas.handles])
  have hLvb : H.Lv ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hnd
  refine ⟨fun a' lo' y' ha' hl' => ?_, fun lo' hlo' hno => ?_, ?_, ?_⟩
  · -- the children
    obtain ⟨a, b, rfl⟩ : ∃ a b, a' = a ++ [b] := by
      rcases List.eq_nil_or_concat a' with h0 | ⟨L, b, h0⟩
      · subst h0; simp at ha'
      · exact ⟨L, b, by simpa using h0⟩
    have ha : a.length = d := by simpa using ha'
    rw [eighLoc_append_singleton] at hl'
    obtain ⟨⟨lo, y⟩, hl, hl2⟩ := Option.bind_eq_some_iff.mp hl'
    simp only [ha, Nat.zero_add] at hl2
    have hk1 : 1 ≤ y.k := by
      by_contra h0
      have h0' : y.k ≤ 1 := by omega
      simp [eighLoc, eighStep, h0'] at hl2
    have hkn := (add_k_le_and_of_eighLoc hl).1
    exact (EighSlotDone.of_read_eq hk1 hkn (fun b i hwin => hpop p b i (lt_of_win hlt hwin))
      (hdne lo y (by omega) ⟨a, ha, hl⟩)).2 b lo' y' hl2
  · -- the slots that start no node
    refine readsIdx_of_read_eq ?_ (hnext lo' hlo')
    rw [hpop p H.Sz _ hSzT, hfre p H.Sz _ ?_ (fun h => by omega), hSz]
    intro lo y _ ⟨a, ha, hl⟩ hwin
    obtain ⟨j, hj, hij⟩ := exists_eq_of_eighSlotWindow_sz hnd hwin
    obtain rfl : j = lo' := by omega
    obtain ⟨b, y', hl2⟩ := exists_eighLoc_of_eighChildSlot hj
    refine hno (a ++ [b]) y' (by simp [ha]) ?_
    rw [eighLoc_append_singleton, hl, Option.bind_some]
    simpa [ha] using hl2
  · rw [hpop p H.Lv _ hLvT, hfre p H.Lv _ (fun _ _ _ _ => not_eighSlotWindow_of_not_mem hLvb)
      (fun h => by omega), hW1]
  · rw [hpop p H.Lv _ hLvT, hfre p H.Lv _ (fun _ _ _ _ => not_eighSlotWindow_of_not_mem hLvb)
      (fun h => by omega), hW2]

omit [AddMonoid C] in
/-- After the slot loop, with the scratch buffer popped, the records of depth $d$ hold and every
cell outside the records of depth $d$, the cells of depth $d + 1$ and the sample buffers `Su`,
`Sg` reads as in the store `S` before the level: from the invariant `DownSlotsInv` at $n$ and the
frame `hrg` of the instructions and draws before the loop. -/
private theorem recordHolds_frame_of_downSlots {p : P} {H : EighArenas} {n F ℓ₀ d tH Su Sg : ℕ}
    {S : Store P K} {s₀ σ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hlt : ∀ x ∈ H.handles, x < tH) (hsz : σ.store.size = tH + 1) (hS : S.size = tH)
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A s₀ σ n)
    (hrg : ∀ q b i, b < tH → b ≠ Su → b ≠ Sg →
      ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      s₀.store.read q b i = S.read q b i) :
    H.RecordHolds I.sem (Array.pop σ.store) p (eighTapeMachine I p mmR qrR) n F R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      ∀ q b i, b ≠ Su → b ≠ Sg →
        ¬ ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) →
        ¬ H.LevelCell n (d + 1) b i → Store.read (Array.pop σ.store) q b i = S.read q b i := by
  obtain ⟨-, -, hdne, hfre⟩ := hinv
  have hpop : ∀ q b i, b < tH → Store.read (Array.pop σ.store) q b i = σ.store.read q b i :=
    fun q b i hb => Store.read_pop_of_lt (by omega)
  refine ⟨fun a lo y ha hl hk1 => ?_, fun q b i hbSu hbSg h1 h2 => ?_⟩
  · have hkn := (add_k_le_and_of_eighLoc hl).1
    exact (EighSlotDone.of_read_eq hk1 hkn (fun b i hwin => hpop p b i (lt_of_win hlt hwin))
      (hdne lo y (by omega) ⟨a, ha, hl⟩)).1
  · by_cases hb : b < tH
    · rw [hpop q b i hb, hfre q b i ?_ (fun h => by omega)]
      · exact hrg q b i hb hbSu hbSg fun h => h2 (Or.inr (Or.inr h))
      · intro lo y hlo ⟨a, ha, hl⟩ hwin
        have hn1 : 1 ≤ n := by omega
        rcases levelCell_of_win (eighLoc_bounds hn1 hl).1 (eighLoc_bounds hn1 hl).2 hwin with
          h | h
        · exact h1 h
        · exact h2 h
    · rw [Store.read_eq_none_of_size_le (s := Array.pop σ.store) (q := q) (b := b) (i := i)
        (by simp [Array.size_pop, hsz]; omega),
        Store.read_eq_none_of_size_le (s := S) (q := q) (b := b) (i := i) (by omega)]

omit [AddMonoid C] [Inhabited K] in
/-- The nodes of depth $d$ transfer to a store that reads the same at `p` on the size and node
arenas and on the window and tolerance cells below $2d + 2$. -/
private theorem levelHolds_of_read_eq {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K}
    {p : P} {M : FloatMachine K ℕ ℕ} {n F ℓ₀ d : ℕ} {R₀ β : K} {root : EighNode K}
    (hs : ∀ b i, (b = H.Ma ∨ b = H.Sz ∨ (b = H.Lv ∧ i < 2 * d + 2)) →
      s'.read p b i = s.read p b i)
    (h : H.LevelHolds sem s p M n F ℓ₀ R₀ β root d) :
    H.LevelHolds sem s' p M n F ℓ₀ R₀ β root d := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun a lo y ha hl => ?_, fun lo hlo hno =>
    readsIdx_of_read_eq (hs _ _ (Or.inr (Or.inl rfl))) (h2 lo hlo hno),
    (hs _ _ (Or.inr (Or.inr ⟨rfl, by omega⟩))).trans h3,
    (hs _ _ (Or.inr (Or.inr ⟨rfl, by omega⟩))).trans h4⟩
  obtain ⟨r1, r2⟩ := h1 a lo y ha hl
  exact ⟨readsIdx_of_read_eq (hs _ _ (Or.inr (Or.inl rfl))) r1,
    pairLayout_holds_of_read_eq r2 fun i _ _ => hs _ _ (Or.inl rfl)⟩

omit [AddMonoid C] [Inhabited K] in
/-- A cell below `b` outside `Su`, `Sg` and the next window cells keeps its value through the head
and the draws. -/
private theorem read_eq_of_stages {p : P} {H : EighArenas} {n d Su Sg b : ℕ} {st s₃ : St P K C}
    (hsz : st.store.size = b)
    (hm : Modifies [(b, 0, 5), (H.Lv, 2 * (d + 1), 2), (Su, 0, n), (Sg, 0, 4 * (n * n))]
      (st.allocate p (5 : IExp ℕ).eval (I.width p)).store s₃.store) (q : P) (x i : ℕ)
    (hxb : x < b) (hxS : x ≠ Su) (hxG : x ≠ Sg)
    (hxL : x ≠ H.Lv ∨ i < 2 * (d + 1) ∨ 2 * (d + 1) + 2 ≤ i) :
    s₃.store.read q x i = st.store.read q x i :=
  (hm.2 q x i (by fp_omega [hxb, hxS, hxG, hxL])).trans
    (St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega))

omit [AddMonoid C] in
/-- The slot loop's precondition holds after the head and the draws: the combined effect on the
allocated store is `hm`, and the draws are stored. -/
private theorem eighDownPre_of_stages {md : Mode} {dec : P → K → ℝ} {p : P} {H : EighArenas}
    {n F ℓ₀ d D par Su Sg c b : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    {st s₃ : St P K C} (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlt : ∀ x ∈ H.handles ++ [par, c], x < b) (hsz : st.store.size = b)
    (hH : H.Shaped st.store p n D)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (hN : md.Needs (0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀ ∧ d < D))
    (hm : Modifies [(b, 0, 5), (H.Lv, 2 * (d + 1), 2), (Su, 0, n), (Sg, 0, 4 * (n * n))]
      (st.allocate p (5 : IExp ℕ).eval (I.width p)).store s₃.store)
    (hSu : ∀ w < n, s₃.store.read p Su w = some (I.tape .uniform (n * d + w)))
    (hSg : ∀ w < 4 * (n * n), s₃.store.read p Sg w =
      some (I.tape .gaussian (4 * (n * n) * d + w))) :
    EighDownPre I mmR qrR md dec p H n F ℓ₀ d D par Su Sg c b A R₀ ε β s₃ := by
  obtain ⟨⟨dLvSu, dLvSg⟩, ⟨dSzSu, dSzSg, dSzLv⟩, ⟨dMaSu, dMaSg, dMaLv⟩, ⟨dparSu, dparSg, dparLv⟩,
    ⟨dcSu, dcSg, dcLv⟩, dSuSg⟩ := downLevel_bufs_ne hbufs
  have hlt' : ∀ x ∈ H.handles, x < b := fun x hx => hlt x (List.mem_append_left _ hx)
  have hLvb : H.Lv < b := hlt' _ (by simp [EighArenas.handles])
  have hMab : H.Ma < b := hlt' _ (by simp [EighArenas.handles])
  have hSzb : H.Sz < b := hlt' _ (by simp [EighArenas.handles])
  have hcb : c < b := hlt c (by simp)
  have hparb : par < b := hlt par (by simp)
  have hrd : ∀ q x i, x < b → x ≠ Su → x ≠ Sg → (x ≠ H.Lv ∨ i < 2 * (d + 1)) →
      s₃.store.read q x i = st.store.read q x i := fun q x i hxb hxS hxG hxL =>
    read_eq_of_stages hsz hm q x i hxb hxS hxG (by omega)
  have hsh : s₃.store.shape = (st.allocate p (5 : IExp ℕ).eval (I.width p)).store.shape := hm.1
  have hsh0 : ∀ x, x < b → s₃.store.shape[x]? = st.store.shape[x]? := fun x hx => by
    rw [hsh]
    exact Store.getElem?_shape_push_of_lt _ (by omega)
  have hT : s₃.store.shape[b]? = some (p, 5) := by
    rw [hsh]
    have := Store.getElem?_shape_push_size st.store p 5
    rwa [hsz] at this
  refine ⟨(Store.size_eq_of_shape_eq hsh).trans (by simp [St.allocate, hsz]),
    EighArenas.Shaped.of_shape_eq (fun x hx => hsh0 x (hlt' x hx)) hH, hT,
    levelHolds_of_read_eq (fun x i hx => ?_) hlev,
    ⟨(hrd p par 0 hparb dparSu dparSg (Or.inl dparLv)).trans hpar.1,
      (hrd p par 2 hparb dparSu dparSg (Or.inl dparLv)).trans hpar.2⟩,
    ⟨(hrd p c 0 hcb dcSu dcSg (Or.inl dcLv)).trans hc.1,
      (hrd p c 1 hcb dcSu dcSg (Or.inl dcLv)).trans hc.2.1,
      (hrd p c 2 hcb dcSu dcSg (Or.inl dcLv)).trans hc.2.2.1,
      (hrd p c 3 hcb dcSu dcSg (Or.inl dcLv)).trans hc.2.2.2.1,
      (hrd p c 4 hcb dcSu dcSg (Or.inl dcLv)).trans hc.2.2.2.2⟩, hSu, hSg, fun hS => ?_,
    fun hS => ?_, hN⟩
  · rcases hx with rfl | rfl | ⟨rfl, hi⟩
    · exact hrd p _ i hMab dMaSu dMaSg (Or.inl dMaLv)
    · exact hrd p _ i hSzb dSzSu dSzSg (Or.inl dSzLv)
    · exact hrd p _ i hLvb dLvSu dLvSg (Or.inr (by omega))
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · omega
    · obtain ⟨len, hl, hi⟩ := Store.exists_getElem?_shape_of_read_eq_some (hSu (n - 1) (by omega))
      rw [hS, hT] at hl
      have := (Prod.mk.inj (Option.some_inj.mp hl)).2
      omega
  · rcases Nat.eq_zero_or_pos (4 * (n * n)) with h0 | hn
    · omega
    · obtain ⟨len, hl, hi⟩ := Store.exists_getElem?_shape_of_read_eq_some
        (hSg (4 * (n * n) - 1) (by omega))
      rw [hS, hT] at hl
      have := (Prod.mk.inj (Option.some_inj.mp hl)).2
      omega

omit [Inhabited K] in
/-- The draws of the level, then a continuation: the $n$ uniform and the $4n^2$ Gaussian words of
the level are drawn into `Su` and `Sg`, which hold the tape values, and the positions advance.
In mode `total` the draws succeed given the two blocks writable. No printed source. -/
theorem wp_eighDownDraws (md : Mode) (p : P) (n d : ℕ) {Su Sg : ℕ} (hSuSg : Su ≠ Sg)
    (rest : Builder P ι ℕ ℕ Unit) {Q : St P K C → Prop} {st : St P K C}
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hW : md.Needs (Writable st.store p Su 0 n ∧ Writable st.store p Sg 0 (4 * (n * n))))
    (hk : ∀ st', Modifies [(Su, 0, n), (Sg, 0, 4 * (n * n))] st.store st'.store →
      (∀ w < n, st'.store.read p Su w = some (I.tape .uniform (n * d + w))) →
      (∀ w < 4 * (n * n), st'.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) →
      st'.pos .uniform = n * d + n → st'.pos .gaussian = 4 * (n * n) * d + 4 * (n * n) →
      Wp md I rest.run Q st') :
    Wp md I (Builder.forRange (.const n)
      (fun i => Builder.ins (.draw p .uniform ⟨Su, .var i⟩)) >>= fun _ =>
      Builder.forRange (4 * (.const n * .const n))
        (fun w => Builder.ins (.draw p .gaussian ⟨Sg, .var w⟩)) >>= fun _ => rest).run Q st := by
  refine (spec_forRange_draw (m := md) (I := I) (p := p) .uniform Su 0 (IExp.const n)
    (fun i => IExp.var i) (fun i => by simp)).wp_bind (st := st) (hW.mono fun h => by
      simpa using h.1) fun st₂ hm₂ h₂ => ?_
  have hu2 : ∀ i < n, st₂.store.read p Su i = some (I.tape .uniform (n * d + i)) := fun i hi => by
    have := h₂.1 i hi
    rw [Nat.zero_add, hpos.1] at this
    exact this
  have hpu2 : st₂.pos = Function.update st.pos .uniform (n * d + n) := by
    rw [h₂.2.2, hpos.1]
    rfl
  refine (spec_forRange_draw (m := md) (I := I) (p := p) .gaussian Sg 0
    (4 * (IExp.const n * IExp.const n)) (fun w => IExp.var w) (fun w => by simp)).wp_bind
    (st := st₂) (hW.mono fun h => by simpa using h.2.of_shape_eq hm₂.1) fun st₃ hm₃ h₃ => ?_
  have hg2 : st₂.pos .gaussian = 4 * (n * n) * d := by rw [hpu2]; simpa using hpos.2
  refine hk st₃ (hm₂.trans hm₃) (fun w hw => ?_) (fun w hw => ?_) ?_ ?_
  · exact (hm₃.2 p Su w (fun y hy => by
      rw [List.mem_singleton] at hy
      subst hy
      exact blockDisjoint_of_fst_ne hSuSg)).trans (hu2 w hw)
  · have := h₃.1 w (by simpa using hw)
    rw [Nat.zero_add, hg2] at this
    exact this
  · rw [h₃.2.2, hpu2]
    simp
  · rw [h₃.2.2, hg2]
    simp

omit [AddMonoid C] in
/-- The conclusion of the level, from the invariant of the slot loop and the effect of the
instructions before it. -/
private theorem eighDownLevel_post {p : P} {H : EighArenas} {n F ℓ₀ d par Su Sg c b : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {st st2 s₃ s₄ : St P K C}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (hlt : ∀ x ∈ H.handles ++ [par, c], x < b)
    (hsz : st.store.size = b)
    (hmod : Modifies [(b, 0, 5), (H.Lv, 2 * (d + 1), 2), (Su, 0, n), (Sg, 0, 4 * (n * n))]
      (st.allocate p (5 : IExp ℕ).eval (I.width p)).store s₃.store)
    (hR1 : s₃.store.read p H.Lv (2 * (d + 1)) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).1)
    (hR2 : s₃.store.read p H.Lv (2 * (d + 1) + 1) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).2)
    (hm₄ : Modifies (eighSlotsFp H n d b) s₃.store s₄.store)
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d b R₀ β ε A s₃ s₄ n)
    (hu : s₃.pos .uniform = n * d + n) (hg : s₃.pos .gaussian = 4 * (n * n) * d + 4 * (n * n))
    (hst2 : st2.store = st.store) (hpos2 : st2.pos = st.pos)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d) :
    ((∀ lo < n, ReadsIdx I.sem st2.store p H.Sz (n * (d + 1) + lo) 0) →
        H.LevelHolds I.sem (s₄.release p (5 : IExp ℕ).eval (I.width p)).store p
          (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1)) ∧
      H.RecordHolds I.sem (s₄.release p (5 : IExp ℕ).eval (I.width p)).store p
        (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (s₄.release p (5 : IExp ℕ).eval (I.width p)).pos .uniform = st2.pos .uniform + n ∧
      (s₄.release p (5 : IExp ℕ).eval (I.width p)).pos .gaussian =
        st2.pos .gaussian + 4 * (n * n) := by
  obtain ⟨⟨dLvSu, dLvSg⟩, ⟨dSzSu, dSzSg, dSzLv⟩, -⟩ := downLevel_bufs_ne hbufs
  have hnd : H.handles.Nodup := hbufs.sublist (List.sublist_append_left _ _)
  have hlt' : ∀ x ∈ H.handles, x < b := fun x hx => hlt x (List.mem_append_left _ hx)
  have hsz4 : s₄.store.size = b + 1 := by
    rw [Store.size_eq_of_shape_eq hm₄.1, Store.size_eq_of_shape_eq hmod.1]
    simp [St.allocate, hsz]
  have hSz : ∀ j, s₃.store.read p H.Sz j = st2.store.read p H.Sz j := fun j => by
    rw [hst2]
    exact read_eq_of_stages hsz hmod p _ j (hlt' _ (by simp [EighArenas.handles])) dSzSu dSzSg
      (Or.inl dSzLv)
  have hrg : ∀ q x i, x < b → x ≠ Su → x ≠ Sg →
      ¬ (x = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      s₃.store.read q x i = st.store.read q x i := fun q x i hxb hxS hxG hxL =>
    read_eq_of_stages hsz hmod q x i hxb hxS hxG (by omega)
  refine ⟨fun hnext => levelHolds_succ_of_downSlots hlt' hnd hsz4 hinv hnext hSz
      hR1 hR2,
    (recordHolds_frame_of_downSlots hlt' hsz4 hsz hinv hrg).1, ?_, ?_⟩
  · change s₄.pos .uniform = st2.pos .uniform + n
    rw [hinv.2.1, hu, hpos2, hpos.1]
  · change s₄.pos .gaussian = st2.pos .gaussian + 4 * (n * n)
    rw [hinv.2.1, hg, hpos2, hpos.2]

omit [AddMonoid C] in
/-- What the head, the draws and the slots modify lies in the footprint of the level and the
scratch buffer. -/
private theorem eighDownFp_sub {H : EighArenas} {n d Su Sg b : ℕ} :
    ∀ x ∈ [(b, 0, 5), (H.Lv, 2 * (d + 1), 2), (Su, 0, n), (Sg, 0, 4 * (n * n))] ++
      eighSlotsFp H n d b, ∃ y ∈ eighDownFp H n d Su Sg ++ [(b, 0, (5 : IExp ℕ).eval)],
      x.1 = y.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.1 + x.2.2 ≤ y.2.1 + y.2.2 := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    eighSlotsFp] at hx
  rcases hx with ((rfl | rfl | rfl | rfl) | ((hx | hx) | rfl))
  · exact ⟨(b, 0, 5), by simp, rfl, by simp, by simp⟩
  · exact ⟨(H.Lv, 2 * (d + 1), 2), by simp [eighDownFp, eighLevelBlocks], rfl, by simp, by simp⟩
  · exact ⟨(Su, 0, n), by simp [eighDownFp], rfl, by simp, by simp⟩
  · exact ⟨(Sg, 0, 4 * (n * n)), by simp [eighDownFp], rfl, by simp, by simp⟩
  · exact ⟨x, by simp [eighDownFp, hx], rfl, by simp, by simp⟩
  · exact ⟨x, by simp [eighDownFp, hx], rfl, by simp, by simp⟩
  · exact ⟨(b, 0, 5), by simp, rfl, by simp, by simp⟩

/-- The level of depth $d$ as a routine specification: from arenas holding the nodes of depth $d$,
with the sizes of depth $d + 1$ reading $0$, the stored parameters and constants, the tape
positions $nd$ and $4n^2 d$, the run of `NLAlib.eighDownLevel` modifies only the records of depth
$d$, the cells of depth $d + 1$ and the sample buffers, leaves the arenas holding the nodes of
depth $d + 1$ and the records of depth $d$, and advances the tape positions by $n$ and $4n^2$. In
mode `total` it also succeeds, given the standard model, $\ell_0 \ge 1$, $R_0 \ge 0$, $d < D$ and
the sample buffers writable. No printed source. -/
theorem spec_eighDownLevel {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d D : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c b : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (hlt : ∀ x ∈ H.handles ++ [par, c], x < b) :
    RoutineSpec md I (fun st => st.store.size = b ∧ H.Shaped st.store p n D ∧
        H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
        (st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d) ∧
        (st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β) ∧
        (st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
          st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
            (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
          st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
            (eighTapeMachine I p mmR qrR).one) ∧
          st.store.read p c 4 = some (I.sem.sqrtHalf p)) ∧
        md.Needs (Writable st.store p Su 0 n ∧ Writable st.store p Sg 0 (4 * (n * n)) ∧
          0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀ ∧ d < D))
      (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su Sg H.Ma H.Ua
        H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
      (eighDownFp H n d Su Sg) fun st st' =>
        ((∀ lo < n, ReadsIdx I.sem st.store p H.Sz (n * (d + 1) + lo) 0) →
          H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
            ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1)) ∧
        H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
        st'.pos .uniform = st.pos .uniform + n ∧
        st'.pos .gaussian = st.pos .gaussian + 4 * (n * n) := by
  unfold eighDownLevel
  refine RoutineSpec.scope (Spec.allocBind_named (b := b) (fun st hst => hst.1) ?_)
  rintro s ⟨st, ⟨hsz, hH, hlev, hpos, hpar, hc, hN⟩, rfl⟩
  obtain ⟨-, o, -, hl1, -, -⟩ := id hflag
  obtain ⟨z₂, hz₂, -⟩ := hlit p 2 (by omega)
  obtain ⟨⟨dLvSu, dLvSg⟩, -, -, -, ⟨-, -, dcLv⟩, dSuSg⟩ := downLevel_bufs_ne hbufs
  have hlt' : ∀ x ∈ H.handles, x < b := fun x hx => hlt x (List.mem_append_left _ hx)
  have hLvb : H.Lv < b := hlt' _ (by simp [EighArenas.handles])
  have hcb : c < b := hlt c (by simp)
  have hal : ∀ q x i, x < b → (st.allocate p (5 : IExp ℕ).eval (I.width p)).store.read q x i =
      st.store.read q x i := fun q x i hx => St.read_allocate_of_lt _ _ _ _ _ _ _ (by omega)
  have hsh0 : ∀ x, x < b → (st.allocate p (5 : IExp ℕ).eval (I.width p)).store.shape[x]? =
      st.store.shape[x]? := fun x hx => Store.getElem?_shape_push_of_lt _ (by omega)
  have hT0 : (st.allocate p (5 : IExp ℕ).eval (I.width p)).store.shape[b]? = some (p, 5) := by
    have := Store.getElem?_shape_push_size st.store p 5
    rwa [hsz] at this
  refine wp_eighDownHead md p n ℓ₀ d D hsem H (R := (eighLevelParams (eighTapeMachine I p mmR qrR)
    R₀ ε ℓ₀ d).1) (ε := (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).2)
    (Nat.ne_of_lt hcb) (Nat.ne_of_lt hLvb) dcLv ⟨o, hl1⟩ ⟨z₂, hz₂⟩ _
    ⟨EighArenas.Shaped.of_shape_eq (fun x hx => hsh0 x (hlt' x hx)) hH, hT0,
      (hal _ _ _ hcb).trans hc.1, (hal _ _ _ hcb).trans hc.2.1,
      (hal _ _ _ hcb).trans hc.2.2.1, (hal _ _ _ hLvb).trans hlev.2.2.1,
      (hal _ _ _ hLvb).trans hlev.2.2.2, hN.mono fun h => ⟨h.2.2.2.1, h.2.2.2.2⟩⟩
    fun st₁ hm₁ hR1 hR2 hp1 => ?_
  refine wp_eighDownDraws md p n d dSuSg _ ⟨(congrFun hp1 .uniform).trans hpos.1,
    (congrFun hp1 .gaussian).trans hpos.2⟩ (hN.mono fun h => ⟨(h.1.push _).of_shape_eq hm₁.1,
      by simpa using (h.2.1.push _).of_shape_eq hm₁.1⟩) fun st₃ hmd hu3 hg3 hpu hpg => ?_
  have hmod : Modifies [(b, 0, 5), (H.Lv, 2 * (d + 1), 2), (Su, 0, n), (Sg, 0, 4 * (n * n))]
      (st.allocate p (5 : IExp ℕ).eval (I.width p)).store st₃.store := by
    refine (hm₁.trans hmd).of_sub fun x hx => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((rfl | rfl) | rfl | rfl)
    · exact ⟨(b, 0, 5), by simp, rfl, by simp, by simp⟩
    · exact ⟨(H.Lv, 2 * (d + 1), 2), by simp, rfl, by simp, by simp⟩
    · exact ⟨(Su, 0, n), by simp, rfl, by simp, by simp⟩
    · exact ⟨(Sg, 0, 4 * (n * n)), by simp, rfl, by simp, by simp⟩
  have hLv : ∀ j, st₃.store.read p H.Lv j = st₁.store.read p H.Lv j := fun j =>
    hmd.2 p _ _ (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact blockDisjoint_of_fst_ne dLvSu
      · exact blockDisjoint_of_fst_ne dLvSg)
  refine (spec_eighDownSlots hmm hqr md p n F ℓ₀ d D hsem hflag hcmp hlit htn H hbufs
    (A := A) (R₀ := R₀) (ε := ε) (β := β) (c := c) (t := b)
    (fun h => lt_irrefl b (hlt b h)) hlt).wp_run (st := st₃)
    (eighDownPre_of_stages hbufs hlt hsz hH hlev hpar hc (hN.mono fun h => ⟨h.2.2.1, h.2.2.2⟩)
      hmod hu3 hg3) fun st₄ hm₄ hinv => ?_
  refine ⟨(hmod.trans hm₄).of_sub eighDownFp_sub, fun st2 hst2 heq => ?_⟩
  exact eighDownLevel_post hbufs hlt hsz hmod ((hLv _).trans hR1) ((hLv _).trans hR2) hm₄ hinv
    hpu hpg (by simpa [St.allocate] using (congrArg (fun s : St P K C => s.store.pop) heq).symm)
    (congrArg (fun s : St P K C => s.pos) heq).symm hpos
/-- One level of the downward pass, with the finer frame: let the kernels of `I` be the routines
`mmR`, `qrR` on interleaved pairs, the semantics decide flags, with exact integer literals up to
$n + 4$ and the exact floor conversion; $M$ = `NLAlib.eighTapeMachine I p mmR qrR` and the root
$(n, \mathbf{A}, R_0, \varepsilon, \ell_0)$. A successful run of `NLAlib.eighDownLevel` at depth
$d$ from a state whose arenas hold the nodes of depth $d$ and whose size cells of depth $d + 1$
all read $0$, with the tape positions $nd$ and $4n^2 d$, the stored $R_0$, $\beta$ in `par` and
the constants in `c`, ends with the arenas holding the nodes of depth $d + 1$ and the records of
depth $d$; of the cells of depth $d$ only the records (bases, outputs, eigenvalues, kinds,
splits) may change, every cell outside depths $d$ and $d + 1$ and the sample buffers `Su`, `Sg`
is unchanged, the store shape too, and the tape positions advance by $n$ and $4n^2$. No printed
source. -/
theorem levelHolds_succ_of_exec_eighDownLevel {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st st' : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hnext : ∀ lo < n, ReadsIdx I.sem st.store p H.Sz (n * (d + 1) + lo) 0)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su Sg
      H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st = some st') :
    H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) ∧
      H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, b ≠ Su → b ≠ Sg →
        ¬ ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) →
        ¬ H.LevelCell n (d + 1) b i → st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos .uniform = st.pos .uniform + n ∧
      st'.pos .gaussian = st.pos .gaussian + 4 * (n * n) := by
  obtain ⟨-, o, -, hl1, -, -⟩ := id hflag
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  have hlt : ∀ x ∈ H.handles ++ [par, c], x < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSzs, hsz hKd, hsz hKp, hsz hLv,
      Store.lt_size_of_read_eq_some hpar.1, Store.lt_size_of_read_eq_some (hc.1.trans hl1)⟩
  obtain ⟨hm, hL, hR, hu, hg⟩ := (spec_eighDownLevel (u := fun _ => 0) (safe := fun _ _ => True)
    hmm hqr .liberal p n ℓ₀ F d D trivial hflag hcmp hlit htn H hbufs hlt).spec.holds_of_exec
    ⟨rfl, hH, hlev, hpos, hpar, hc, trivial⟩ h
  refine ⟨hL hnext, hR, fun q b i hSu hSg hrec hlev' => hm.2 q b i fun x hx => ?_, hm.1, hu, hg⟩
  have hnd' : H.handles.Nodup := hnd
  simp only [eighDownFp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | hx | hx
  · exact (blockDisjoint_eighRecordBlocks_iff hnd').mpr hrec x hx
  · exact (blockDisjoint_eighLevelBlocks_iff.mpr hlev') x hx
  · rw [hx]
    exact blockDisjoint_of_fst_ne hSu
  · rw [hx]
    exact blockDisjoint_of_fst_ne hSg

/-- One level of the downward pass: let the kernels of `I` be the routines `mmR`, `qrR` on
interleaved pairs, the semantics decide flags, with exact integer literals up to $n + 4$ and the
exact floor conversion; $M$ = `NLAlib.eighTapeMachine I p mmR qrR` and the root
$(n, \mathbf{A}, R_0, \varepsilon, \ell_0)$. A successful run of `NLAlib.eighDownLevel` at depth
$d$ from a state whose arenas hold the nodes of depth $d$ (`NLAlib.EighArenas.LevelHolds`) and
whose size cells of depth $d + 1$ all read $0$, with the tape positions $nd$ (uniform) and
$4n^2 d$ (Gaussian), the stored $R_0$, $\varepsilon$, $\beta$ in `par` and the constants in `c`
(cells $0$ to $4$: one, $\mathrm{fl}(2)$, $\mathrm{fl}(1/2)$, $-1$, the stored $\sqrt{1/2}$),
ends with the arenas holding the nodes of depth $d + 1$ and the
records of depth $d$ (`NLAlib.EighArenas.RecordHolds`); every cell outside depths $d$ and $d + 1$ of
the arenas and the sample buffers `Su`, `Sg` is unchanged, the store shape too, and the tape
positions advance by $n$ and $4n^2$. No printed source. -/
theorem holds_of_exec_eighDownLevel {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st st' : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hnext : ∀ lo < n, ReadsIdx I.sem st.store p H.Sz (n * (d + 1) + lo) 0)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su Sg
      H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st = some st') :
    H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) ∧
      H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, b ≠ Su → b ≠ Sg → ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos .uniform = st.pos .uniform + n ∧
      st'.pos .gaussian = st.pos .gaussian + 4 * (n * n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := levelHolds_succ_of_exec_eighDownLevel hmm hqr p hflag hcmp n ℓ₀
    F d D hlit htn H hH hbufs hlev hnext hpos hpar hc h
  exact ⟨h1, h2, fun q b i hSu hSg hd1 hd2 => h3 q b i hSu hSg (fun h => hd1 h.2) hd2, h4, h5, h6⟩

end NLAlib
