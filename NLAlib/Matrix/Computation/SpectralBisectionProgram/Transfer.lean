/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownSlot

/-!
# The passes of the spectral bisection program at index variables

Facts the refinement of `NLAlib.eighProg` uses to chain its levels: a cell of the arenas lies at one
depth only, the holding predicates of the arenas transfer between stores that agree on their cells,
the instructions of the initialisation keep them, and each level at an index variable runs as at the
constant of its value.

## Main results

* `NLAlib.exec_eighDownLevel_var`, `NLAlib.exec_eighBottomLevel_of_eval_eq`,
  `NLAlib.exec_eighUpLevel_of_eval_eq`: the levels at index variables.
* `NLAlib.EighArenas.LevelHolds.of_read_eq`, `NLAlib.EighArenas.RecordHolds.of_read_eq`: the
  transfer of the holding predicates.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! ### The program -/

/-! #### Helpers of `NLAlib.holds_of_exec_eighProg` -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell of the arenas lies at one depth only. -/
theorem eq_of_levelCell_of_levelCell {H : EighArenas} (hnd : H.handles.Nodup) {n d e b i : ℕ}
    (h1 : H.LevelCell n d b i) (h2 : H.LevelCell n e b i) : d = e := by
  have hm : ∀ m x y : ℕ, m * x ≤ i → i < m * (x + 1) → m * y ≤ i → i < m * (y + 1) → x = y := by
    intro m x y h1 h2 h3 h4
    by_contra hxy
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · have := Nat.mul_le_mul_left m (show x + 1 ≤ y by omega); omega
    · have := Nat.mul_le_mul_left m (show y + 1 ≤ x by omega); omega
  simp only [EighArenas.handles, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨_, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _⟩,
    ⟨_, _⟩, _, -⟩ := hnd
  unfold EighArenas.LevelCell at h1 h2
  rcases h1 with ⟨hb1, a1, a2⟩ | ⟨hb1, a1, a2⟩ | ⟨hb1, a1⟩ <;>
    rcases h2 with ⟨hb2, c1, c2⟩ | ⟨hb2, c1, c2⟩ | ⟨hb2, c1⟩
  · exact hm _ _ _ a1 a2 c1 c2
  · exfalso
    rcases hb1 with h | h | h <;> rcases hb2 with h' | h' | h' | h' <;>
      exact absurd (h.symm.trans h') ‹_›
  · exfalso
    rcases hb1 with h | h | h <;> exact absurd (h.symm.trans hb2) ‹_›
  · exfalso
    rcases hb2 with h' | h' | h' <;> rcases hb1 with h | h | h | h <;>
      first | exact absurd (h.symm.trans h') ‹_› | exact absurd (h'.symm.trans h) ‹_›
  · exact hm _ _ _ a1 a2 c1 c2
  · exfalso
    rcases hb1 with h | h | h | h <;> exact absurd (h.symm.trans hb2) ‹_›
  · exfalso
    rcases hb2 with h | h | h <;> exact absurd (h.symm.trans hb1) ‹_›
  · exfalso
    rcases hb2 with h | h | h | h <;> exact absurd (h.symm.trans hb1) ‹_›
  · omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A block of at most $k^2$ complex words at the slot of a node of size $k$ lies at its
depth. -/
private theorem lt_of_block_le {n d lo k i : ℕ} (hk : lo + k ≤ n)
    (h1 : 2 * (n * n) * d + 2 * n * lo ≤ i) (h2 : i < 2 * (n * n) * d + 2 * n * lo + 2 * (k * k)) :
    2 * (n * n) * d ≤ i ∧ i < 2 * (n * n) * (d + 1) := by
  have e1 : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have e2 : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  constructor <;> nlinarith

omit [AddMonoid C] [Inhabited K] in
/-- The nodes of depth $e$ transfer to a store that reads the same on the node, size and window
cells of depth $e$ and on the size cell $ne$ (the root's when $n = 0$). No printed source. -/
theorem EighArenas.LevelHolds.of_read_eq {H : EighArenas} {s s' : Store P K} {p : P}
    {sem : ScalarSem P K} {M : FloatMachine K ℕ ℕ} {n F ℓ₀ e : ℕ} {R₀ β ε : K}
    {A : Matrix (Fin n) (Fin n) (K × K)}
    (hs : ∀ q b i, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) →
      (H.LevelCell n e b i ∨ (b = H.Sz ∧ i = n * e)) → s'.read q b i = s.read q b i)
    (h : H.LevelHolds sem s p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e) :
    H.LevelHolds sem s' p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e := by
  have e4 : n * (e + 1) = n * e + n := by ring
  refine ⟨fun a lo y ha hay => ?_, fun lo hlo hno => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 a lo y ha hay
    obtain ⟨hb, hb1⟩ := add_k_le_and_of_eighLoc hay
    refine ⟨readsIdx_of_read_eq (hs p _ _ (Or.inr (Or.inl rfl)) ?_) h1,
      pairLayout_holds_of_read_eq h2 fun i h1' h2' => hs p _ _ (Or.inl rfl) ?_⟩
    · by_cases hlo : lo = 0
      · exact Or.inr ⟨rfl, by omega⟩
      · have := hb1 (by omega)
        exact Or.inl (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by omega⟩))
    · exact Or.inl (Or.inl ⟨Or.inl rfl, lt_of_block_le hb h1' h2'⟩)
  · exact readsIdx_of_read_eq (hs p _ _ (Or.inr (Or.inl rfl))
      (Or.inl (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by omega⟩)))) (h.2.1 lo hlo hno)
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inl (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)))]
    exact h.2.2.1
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inl (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)))]
    exact h.2.2.2

omit [AddMonoid C] [Inhabited K] in
/-- The records of depth $d$ transfer to a store that reads the same on the output, basis,
eigenvalue, kind and split cells of depth $d$. No printed source. -/
theorem EighArenas.RecordHolds.of_read_eq {H : EighArenas} {sem : ScalarSem P K}
    {s s' : Store P K} {p : P} {M : FloatMachine K ℕ ℕ} {n F ℓ₀ d : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hs : ∀ q b i, (b = H.Ua ∨ b = H.Qa ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) →
      H.LevelCell n d b i → s'.read q b i = s.read q b i)
    (h : H.RecordHolds sem s p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.RecordHolds sem s' p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  have e4 : n * (d + 1) = n * d + n := by ring
  intro a lo y ha hl hk
  have hkn := (add_k_le_and_of_eighLoc hl).1
  have hR : ∀ {b} k, (b = H.Kd ∨ b = H.Kp) → ReadsIdx sem s p b (n * d + lo) k →
      ReadsIdx sem s' p b (n * d + lo) k := fun k hb hr =>
    readsIdx_of_read_eq (hs p _ _ (by rcases hb with h | h <;> simp [h])
      (Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩))) hr
  have hblk : ∀ {b} {l m : ℕ} {Y : Matrix (Fin l) (Fin m) (K × K)} (off : ℕ),
      (b = H.Ua ∨ b = H.Qa) → off + 2 * (l * m) ≤ 2 * (y.k * y.k) →
      pairLayout.Holds s p b (2 * (n * n) * d + 2 * n * lo + off) Y →
      pairLayout.Holds s' p b (2 * (n * n) * d + 2 * n * lo + off) Y :=
    fun off hb hle hY => pairLayout_holds_of_read_eq hY fun i hi1 hi2 =>
      hs p _ _ (by rcases hb with h | h <;> simp [h])
        (Or.inl ⟨by rcases hb with h | h <;> simp [h], lt_of_block_le hkn (by omega) (by omega)⟩)
  have this := h a lo y ha hl hk
  revert this
  cases eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    rintro ⟨h1, h2, h3⟩
    refine ⟨hR 1 (Or.inl rfl) h1, ?_, fun i => (hs p _ _ (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inr (Or.inl ⟨Or.inl rfl, by omega, by have := i.isLt; omega⟩))).trans (h3 i)⟩
    simpa using hblk (Y := U) 0 (Or.inl rfl) (by omega) (by simpa using h2)
  | shift b A' σ => exact hR _ (Or.inl rfl)
  | split kp hkp Qp Qm Ap Am σ =>
    rintro ⟨h1, h2, h3, h4⟩
    have e5 : y.k * kp + y.k * (y.k - kp) = y.k * y.k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hkp]
    have e6 : y.k * kp ≤ y.k * y.k := Nat.mul_le_mul_left _ hkp
    refine ⟨hR 4 (Or.inl rfl) h1, hR kp (Or.inr rfl) h2, ?_, hblk (Y := Qm) _ (Or.inr rfl)
      (by omega) h4⟩
    simpa using hblk (Y := Qp) 0 (Or.inr rfl) (by omega) (by simpa using h3)

omit [Inhabited K] in
/-- A builder that emits one statement before its continuation runs as itself under continuations
that run the same. -/
private theorem BuilderEquiv.refl_seq {X : Builder P ι ℕ ℕ Unit}
    (hX : ∃ S, ∀ k : Unit → Stmt P ι ℕ ℕ, ContT.run X k = .seq S (k ())) : BuilderEquiv I X X := by
  obtain ⟨S, hX⟩ := hX
  intro k k' hk st
  refine (congrArg (exec I · st) (hX k)).trans
    (Eq.trans ?_ (congrArg (exec I · st) (hX k')).symm)
  rw [exec_seq, exec_seq]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
/-- A level of the downward pass at an index variable runs as at the constant of its
value. -/
theorem exec_eighDownLevel_var (p : P) (mm qr : ι)
    (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c : ℕ) (st : St P K C) :
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par Lv Su Sg Ma
      Ua Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st := by
  -- The whole level has too large a normal form for one `rfl`: walk its statements; the blocks
  -- that do not mention the depth are equal as they stand.
  have hE : BuilderEquiv I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv
      Su Sg Ma Ua Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
      (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) := by
    unfold eighDownLevel
    repeat' first
      | exact BuilderEquiv.pure
      | (with_reducible refine BuilderEquiv.refl_seq ?_); exact ⟨_, fun _ => rfl⟩
      | apply BuilderEquiv.bind
      | apply BuilderEquiv.ins
      | apply BuilderEquiv.kcall
      | apply BuilderEquiv.forRange
      | apply BuilderEquiv.bindIdx
      | apply BuilderEquiv.ite
      | apply BuilderEquiv.named
      | apply BuilderEquiv.scope
      | apply BuilderEquiv.allocBind
      | intro _
      | rfl
  exact hE (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

omit [Inhabited K] in
/-- The spent level at an index expression runs as at the constant of its value. -/
theorem exec_eighBottomLevel_of_eval_eq (p : P) (n D : ℕ) (De : IExp ℕ) (hD : De.eval = D)
    (Ua Ea Sz : ℕ) (st : St P K C) :
    exec I (eighBottomLevel (ι := ι) p (.const n) De Ua Ea Sz).run st =
      exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) Ua Ea Sz).run st := by
  subst hD
  exact exec_eq_of_normIdx_eq I (by unfold eighBottomLevel zidentity; rfl) st

omit [Inhabited K] in
/-- A level of the upward pass at an index expression runs as at the constant of its
value. -/
theorem exec_eighUpLevel_of_eval_eq (p : P) (mm : ι) (n d : ℕ) (de : IExp ℕ) (hd : de.eval = d)
    (Lv Ua Qa Ea Sz Kd Kp c : ℕ) (st : St P K C) :
    exec I (eighUpLevel p mm (.const n) de Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run st =
      exec I (eighUpLevel p mm (.const n) (.const d) Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run st := by
  subst hd
  exact exec_eq_of_normIdx_eq I rfl st

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The node, size and window arenas are arenas. -/
theorem mem_handles_of_node_arena {H : EighArenas} {b : ℕ} (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) :
    b ∈ H.handles := by
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The record arenas are arenas. -/
theorem mem_handles_of_record_arena {H : EighArenas} {b : ℕ}
    (h : b = H.Ua ∨ b = H.Qa ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) : b ∈ H.handles := by
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h | h <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The node, size and window arenas are not record arenas. -/
theorem false_of_node_arena_of_record_arena {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv)
    (h' : b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) : False := by
  rcases h with rfl | rfl | rfl <;> rcases h' with h' | h' | h' | h' | h' <;>
    simp [EighArenas.handles, h'] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The node, size and window arenas are not the output or eigenvalue arenas. -/
theorem false_of_node_arena_of_out_arena {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) (h' : b = H.Ua ∨ b = H.Ea) : False :=
  false_of_node_arena_of_record_arena hnd h (by rcases h' with h' | h' <;> simp [h'])

/-! ### The arenas as footprints and the transfer of the level predicates -/

/-- Two intervals of one length at distinct multiples are disjoint. -/
private theorem eq_of_mul_le_of_lt_mul {m e e' i : ℕ} (h1 : m * e ≤ i) (h2 : i < m * (e + 1))
    (h3 : m * e' ≤ i)
    (h4 : i < m * (e' + 1)) : e = e' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := Nat.mul_le_mul_left m (show e + 1 ≤ e' by omega); omega
  · have := Nat.mul_le_mul_left m (show e' + 1 ≤ e by omega); omega

/-- The cells of distinct depths are distinct. -/
theorem not_levelCell_of_ne {H : EighArenas} (hnd : H.handles.Nodup) {n e e' b i : ℕ}
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

/-- A buffer outside the arenas is not one of them. -/
theorem not_mem_handles_of_mem {H : EighArenas} {l : List ℕ} (h : (H.handles ++ l).Nodup)
    {x : ℕ}
    (hx : x ∈ l) : x ∉ H.handles := fun hm => List.disjoint_of_nodup_append h hm hx

/-- The size cell $ne$ is not a cell of a deeper depth. -/
theorem not_levelCell_sz {H : EighArenas} (hnd : H.handles.Nodup) {n e d : ℕ} (he : e < d) :
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
theorem not_levelCell_sz_of_le {H : EighArenas} (hnd : H.handles.Nodup) {n d j : ℕ}
    (hj : n * (d + 1) ≤ j) : ¬ H.LevelCell n d H.Sz j := by
  unfold EighArenas.LevelCell
  rintro (⟨hb, -⟩ | ⟨-, h1, h2⟩ | ⟨hb, -⟩)
  · rcases hb with h | h | h <;> simp [EighArenas.handles, h] at hnd
  · omega
  · simp [EighArenas.handles, hb] at hnd

/-- A cell the node transfer reads is not a cell of a deeper depth. -/
theorem not_levelCell_of_lt {H : EighArenas} (hnd : H.handles.Nodup) {n e d b i : ℕ}
    (he : e < d)
    (hi : H.LevelCell n e b i ∨ (b = H.Sz ∧ i = n * e)) : ¬ H.LevelCell n d b i := by
  rcases hi with hi | ⟨rfl, rfl⟩
  · exact not_levelCell_of_ne hnd (by omega) hi
  · exact not_levelCell_sz hnd he


/-- **The arenas and sample buffers of the driver, whole**, each with the cells of $D + 1$ levels
(the bases, kinds and splits have only $D$ levels, but the last level of the downward pass is
within the footprint of `NLAlib.eighDownFp`). -/
def eighArenaFp (H : EighArenas) (n D Su Sg : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(H.Ma, 0, 2 * (n * n) * (D + 1)), (H.Ua, 0, 2 * (n * n) * (D + 1)),
    (H.Qa, 0, 2 * (n * n) * (D + 1)), (H.Ea, 0, n * (D + 1)), (H.Sz, 0, n * (D + 1) + 1),
    (H.Kd, 0, n * (D + 1)), (H.Kp, 0, n * (D + 1)), (H.Lv, 0, 2 * (D + 1)), (Su, 0, n),
    (Sg, 0, 4 * (n * n))]

/-- The output and eigenvalue blocks of one level up to depth $D$ lie in the arenas. -/
theorem eighOutFp_sub_arena {H : EighArenas} {n d D Su Sg : ℕ} (hd : d ≤ D) :
    ∀ x ∈ [(H.Ua, 2 * (n * n) * d, 2 * (n * n)), (H.Ea, n * d, n)], ∃ y ∈ eighArenaFp H n D Su Sg,
      x.1 = y.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.1 + x.2.2 ≤ y.2.1 + y.2.2 := by
  have f1 : 2 * (n * n) * d + 2 * (n * n) ≤ 2 * (n * n) * (D + 1) := by
    have := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ D + 1 by omega); nlinarith
  have f3 : n * d + n ≤ n * (D + 1) := by
    have := Nat.mul_le_mul_left n (show d + 1 ≤ D + 1 by omega); nlinarith
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨(H.Ua, 0, 2 * (n * n) * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Ea, 0, n * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩


omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A buffer that is neither an arena nor a sample buffer is disjoint from the arenas. -/
theorem fst_ne_of_mem_eighArenaFp {H : EighArenas} {n D Su Sg b : ℕ} (hb : b ∉ H.handles)
    (h1 : b ≠ Su) (h2 : b ≠ Sg) : ∀ x ∈ eighArenaFp H n D Su Sg, b ≠ x.1 := by
  intro x hx h
  simp only [eighArenaFp, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h1 h | exact h2 h
    | exact hb (by simp [EighArenas.handles, h])

omit [AddMonoid C] [Inhabited K] in
/-- A change confined to the arenas keeps every other buffer. -/
theorem read_eq_of_modifies_eighArenaFp {H : EighArenas} {n D Su Sg b i : ℕ} {s s' : Store P K}
    {q : P} (hm : Modifies (eighArenaFp H n D Su Sg) s s') (hb : b ∉ H.handles) (h1 : b ≠ Su)
    (h2 : b ≠ Sg) : s'.read q b i = s.read q b i :=
  hm.2 q b i fun x hx => blockDisjoint_of_fst_ne (fst_ne_of_mem_eighArenaFp hb h1 h2 x hx)


omit [AddMonoid C] [Inhabited K] in
/-- **The root at depth $0$**: a store whose size arena holds $n \ge 1$ in its cell $0$ and $0$ in
its cells $1, \ldots, n(\ell_0 + 2)$, whose node arena holds $\mathbf{A}$ at offset $0$ and whose
window arena holds $R_0$, $\varepsilon$ in its cells $0$, $1$ holds the nodes of depth $0$, under
exact integer literals up to $n + 4$ and the exact floor conversion. -/
theorem levelHolds_zero_of_init {dec : P → K → ℝ} {p : P} {M : FloatMachine K ℕ ℕ}
    {n ℓ₀ F : ℕ} (hlit : IsExactIntLit dec I.sem (n + 4))
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

/-- **The root's output of the shallow recursion on the samples at the slots**: `NLAlib.eigh` on
the machine of the interpretation. -/
noncomputable def eighSlotOut (I : Interp P ι K C) (p : P) (mmR : MatMulMap (K × K))
    (qrR : QRMap (K × K)) (n F ℓ₀ : ℕ) (A₀ : Matrix (Fin n) (Fin n) (K × K)) (R₀ ε β : K) :
    Matrix (Fin n) (Fin n) (K × K) × (Fin n → K) :=
  eigh (eighTapeMachine I p mmR qrR) F ℓ₀ A₀ R₀ ε β
    (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A₀, R₀, ε, ℓ₀⟩)

end NLAlib
