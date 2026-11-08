/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames
public import NLAlib.Computation.IndexBinder
public import NLAlib.Computation.Loops
public import NLAlib.Computation.Contract
public import NLAlib.Computation.StaticCost
public import NLAlib.Computation.ExecCharge
public import NLAlib.Computation.MatvecRoutine

/-!
# A program logic for runs

A program logic for `NLAlib.Computation.exec` (design note
`docs/design/Computation-ProgramLogic.md`). The run `NLAlib.Computation.exec` is
deterministic, so its weakest precondition is a definition, not an inductive judgement:
`NLAlib.Computation.Wp m I s Q st` says the run of `s` from `st` ends in a state satisfying `Q`
(mode `total`: it succeeds; mode `liberal`: if it succeeds). A triple
(`NLAlib.Computation.Triple`) relates the start and final states, so frames, counts and the
size of the store are stated against the start state, and a routine specification
(`NLAlib.Computation.Spec`) adds the blocks it may modify (`NLAlib.Computation.Modifies`). The
rules are proved once from the run equations of `NLAlib/Computation/Exec.lean`; a program proof
applies them statement by statement, each step naming the next state.

## Main definitions

* `NLAlib.Computation.Modifies`, `NLAlib.Computation.ReadsOnly`: footprints and read sets.
* `NLAlib.Computation.Mode`, `NLAlib.Computation.Wp`, `NLAlib.Computation.Triple`: the logic.
* `NLAlib.Computation.Spec`, `NLAlib.Computation.RoutineSpec`: routine specifications.
* `NLAlib.Computation.Costs`: an exact count, threaded additively.
* `NLAlib.Computation.matBlock`: the canonical block of a stored matrix.
* `NLAlib.Computation.PosKept`, `NLAlib.Computation.CostsLe`: kept tape positions, a weighted
  count bound.

## Main results

* `NLAlib.Computation.wp_seq`, `NLAlib.Computation.wp_alloc`, `NLAlib.Computation.wp_ite`,
  `NLAlib.Computation.wp_bindIdx_of_read`, `NLAlib.Computation.wp_kcall`: the statement rules.
* `NLAlib.Computation.Triple.loop`, `NLAlib.Computation.Triple.whileFuel`: invariant rules.
* `NLAlib.Computation.Spec.seq`, `NLAlib.Computation.Spec.frame`,
  `NLAlib.Computation.Spec.alloc`: composition, the frame rule, scoped scratch.
* `NLAlib.Computation.RoutineSpec.wp_bind`: the call rule.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P]

/-! ### Footprints and read sets -/

section Footprint

/-- **`s'` differs from `s` only in the blocks `fp`** (`(handle, offset, length)`): the two stores
have the same shape and every cell disjoint from every block of `fp` reads the same at every
tag. The cell form `blockDisjoint (b, i, 1) x` is the frame form of the kernel contracts. -/
def Modifies (fp : List (ℕ × ℕ × ℕ)) (s s' : Store P K) : Prop :=
  s'.shape = s.shape ∧
    ∀ q b i, (∀ x ∈ fp, blockDisjoint (b, i, 1) x = true) → s'.read q b i = s.read q b i

/-- **A store predicate that reads only the blocks `rs`**: it survives any store that has the
same shape on the buffers of `rs` and reads the same on every cell of `rs`, at every tag. The
block analogue of `NLAlib.Computation.IsFramed`, which reads whole buffers. -/
def ReadsOnly (F : Store P K → Prop) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ s s', F s → (∀ x ∈ rs, s'.shape[x.1]? = s.shape[x.1]?) →
    (∀ q, ∀ x ∈ rs, ∀ j < x.2.2, s'.read q x.1 (x.2.1 + j) = s.read q x.1 (x.2.1 + j)) → F s'

/-- Every block of `rs` is disjoint from every block of `fp`; with
`NLAlib.Computation.blockDisjoint_iff` the goal is linear arithmetic. -/
def BlocksDisjoint (rs fp : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ x ∈ rs, ∀ y ∈ fp, blockDisjoint x y = true

/-- A store modifies nothing of itself. -/
theorem Modifies.refl (fp : List (ℕ × ℕ × ℕ)) (s : Store P K) : Modifies fp s s :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

/-- Footprints in sequence add. -/
theorem Modifies.trans {fp₁ fp₂ : List (ℕ × ℕ × ℕ)} {s s₁ s₂ : Store P K}
    (h₁ : Modifies fp₁ s s₁) (h₂ : Modifies fp₂ s₁ s₂) : Modifies (fp₁ ++ fp₂) s s₂ :=
  ⟨h₂.1.trans h₁.1, fun q b i hb => (h₂.2 q b i fun x hx => hb x (List.mem_append_right _ hx)).trans
    (h₁.2 q b i fun x hx => hb x (List.mem_append_left _ hx))⟩

/-- A footprint may be enlarged. -/
theorem Modifies.mono {fp fp' : List (ℕ × ℕ × ℕ)} {s s' : Store P K} (h : Modifies fp s s')
    (hfp : ∀ x ∈ fp, x ∈ fp') : Modifies fp' s s' :=
  ⟨h.1, fun q b i hb => h.2 q b i fun x hx => hb x (hfp x hx)⟩

/-- A footprint may be replaced by one that covers its cells: every cell disjoint from `fp'` is
disjoint from `fp`. -/
theorem Modifies.of_cells {fp fp' : List (ℕ × ℕ × ℕ)} {s s' : Store P K} (h : Modifies fp s s')
    (hc : ∀ b i, (∀ x ∈ fp', blockDisjoint (b, i, 1) x = true) →
      ∀ x ∈ fp, blockDisjoint (b, i, 1) x = true) : Modifies fp' s s' :=
  ⟨h.1, fun q b i hb => h.2 q b i (hc b i hb)⟩

/-- A scalar write modifies its cell. -/
theorem Modifies.of_write {p : P} {b i : ℕ} {v : K} {s s' : Store P K}
    (h : s.write p b i v = some s') : Modifies [(b, i, 1)] s s' := by
  refine ⟨Store.shape_of_write_eq_some h, fun q b' i' hb =>
    Store.read_of_write_eq_some_of_ne h ?_⟩
  have := blockDisjoint_iff.mp (hb _ List.mem_cons_self)
  dsimp only at this
  omega

/-- Block writes modify their blocks. -/
theorem Modifies.of_writeBlocks {p : P} {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)}
    {s s' : Store P K} (h : s.writeBlocks p bs ys = some s') : Modifies bs s s' := by
  refine ⟨Store.shape_of_writeBlocks_eq_some h, fun q b i hb =>
    Store.read_of_writeBlocks_eq_some_of_forall h fun x hx => ?_⟩
  have := blockDisjoint_iff.mp (hb x hx)
  dsimp only at this
  omega

/-- A block write modifies its block. -/
theorem Modifies.of_writeBlock {p : P} {b o : ℕ} {y : Array K} {s s' : Store P K}
    (h : s.writeBlock p b o y = some s') : Modifies [(b, o, y.size)] s s' := by
  refine ⟨Store.shape_of_writeBlock_eq_some h, fun q b' i hb =>
    Store.read_of_writeBlock_eq_some_of_ne h ?_⟩
  have := blockDisjoint_iff.mp (hb _ List.mem_cons_self)
  dsimp only at this
  omega

/-- A kernel call modifies its output blocks. -/
theorem Modifies.of_kcallStore {C : Type} {I : Interp P ι K C} {o : ι} {p : P} {ds : List ℕ}
    {ins outs : List (ℕ × ℕ)} {s s' : Store P K} (h : I.kcallStore o p ds ins outs s = some s') :
    Modifies (kcallBlocks outs (I.kshape o ds).2) s s' := by
  unfold Interp.kcallStore at h
  split_ifs at h
  obtain ⟨xs, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ys, -, h⟩ := Option.bind_eq_some_iff.mp h
  exact Modifies.of_writeBlocks h

/-- **The frame of a read set**: a predicate that reads only `rs` survives a change confined to
blocks disjoint from `rs`. -/
theorem ReadsOnly.of_modifies {F : Store P K → Prop} {rs fp : List (ℕ × ℕ × ℕ)}
    {s s' : Store P K} (hF : ReadsOnly F rs) (h : F s) (hm : Modifies fp s s')
    (hd : BlocksDisjoint rs fp) : F s' := by
  refine hF s s' h (fun x _ => by rw [hm.1]) fun q x hx j hj => hm.2 q _ _ fun y hy => ?_
  have := blockDisjoint_iff.mp (hd x hx y hy)
  rw [blockDisjoint_iff]
  dsimp only at this ⊢
  omega

/-- A conjunction reads the union of the read sets. -/
theorem ReadsOnly.and {F G : Store P K → Prop} {rs ts : List (ℕ × ℕ × ℕ)} (hF : ReadsOnly F rs)
    (hG : ReadsOnly G ts) : ReadsOnly (fun s => F s ∧ G s) (rs ++ ts) :=
  fun s s' h hsh hrd => ⟨hF s s' h.1 (fun x hx => hsh x (List.mem_append_left _ hx))
      fun q x hx => hrd q x (List.mem_append_left _ hx),
    hG s s' h.2 (fun x hx => hsh x (List.mem_append_right _ hx))
      fun q x hx => hrd q x (List.mem_append_right _ hx)⟩

/-- A read set may be enlarged. -/
theorem ReadsOnly.mono {F : Store P K → Prop} {rs ts : List (ℕ × ℕ × ℕ)} (hF : ReadsOnly F rs)
    (h : ∀ x ∈ rs, x ∈ ts) : ReadsOnly F ts :=
  fun s s' hs hsh hrd => hF s s' hs (fun x hx => hsh x (h x hx)) fun q x hx => hrd q x (h x hx)

/-- A predicate reading only buffers below the top survives pushing a buffer. -/
theorem ReadsOnly.push {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {s : Store P K}
    (hF : ReadsOnly F rs) (h : F s) (hrs : ∀ x ∈ rs, x.1 < s.size) (y : P × Array (Option K)) :
    F (s.push y) :=
  hF s _ h (fun x hx => Store.getElem?_shape_push_of_lt y (hrs x hx)) fun _ x hx _ _ =>
    Store.read_push_of_ne (Nat.ne_of_lt (hrs x hx))

/-- A predicate reading only buffers below the top survives popping the top buffer. -/
theorem ReadsOnly.pop {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {s : Store P K}
    (hF : ReadsOnly F rs) (h : F s) (hrs : ∀ x ∈ rs, x.1 + 1 < s.size) : F s.pop := by
  refine hF s _ h (fun x hx => ?_) fun _ x hx _ _ =>
    Store.read_pop_of_lt (by have := hrs x hx; omega)
  have := hrs x hx
  rw [Store.shape_pop, Array.getElem?_pop, if_pos (by rw [Store.size_shape]; omega)]

/-- One stored cell reads only itself. -/
theorem readsOnly_read (q : P) (b i : ℕ) (v : Option K) :
    ReadsOnly (fun s : Store P K => s.read q b i = v) [(b, i, 1)] :=
  fun s s' hs _ hrd => by simpa using (hrd q (b, i, 1) List.mem_cons_self 0 Nat.one_pos).trans hs

/-- A writable block reads only itself (its shape). -/
theorem readsOnly_writable (p : P) (b off n : ℕ) :
    ReadsOnly (fun s : Store P K => Writable s p b off n) [(b, off, n)] :=
  fun _ _ hs hsh _ => hs.of_getElem?_shape_eq (hsh _ List.mem_cons_self)

/-- A decoded vector reads only its block. -/
theorem readsOnly_readsDecoded {N : ℕ} (dec : P → K → ℝ) (p : P) (b off : ℕ) (x : Fin N → ℝ) :
    ReadsOnly (fun s : Store P K => ReadsDecoded s dec p b off x) [(b, off, N)] :=
  fun _ _ hs _ hrd => hs.of_read_eq fun i hi => hrd p _ List.mem_cons_self i hi

/-- A decoded matrix reads only its block. -/
theorem readsOnly_holdsDecoded {N k : ℕ} (dec : P → K → ℝ) (p : P) (b off : ℕ)
    (M : Matrix (Fin N) (Fin k) ℝ) :
    ReadsOnly (fun s : Store P K => HoldsDecoded s dec p b off M) [(b, off, N * k)] := by
  intro s s' hs _ hrd i j
  obtain ⟨w, hw, hd⟩ := hs i j
  have hij : (i : ℕ) + N * j < N * k := by nlinarith [i.2, j.2]
  refine ⟨w, ?_, hd⟩
  have := hrd p _ List.mem_cons_self _ hij
  simp only [← Nat.add_assoc] at this
  rw [this, hw]

/-- A buffer-framed precondition survives a change confined to other buffers. -/
theorem IsFramed.of_modifies {pre : Store P K → Prop} {ro : List ℕ} {fp : List (ℕ × ℕ × ℕ)}
    {s s' : Store P K} (hf : IsFramed pre ro) (h : pre s) (hm : Modifies fp s s')
    (hro : ∀ x ∈ fp, x.1 ∉ ro) : pre s' := by
  refine hf s s' h (fun _ _ => by rw [hm.1]) fun q b hb i => hm.2 q b i fun x hx => ?_
  exact blockDisjoint_iff.mpr (Or.inl fun he => hro x hx (he ▸ hb))

/-- **The canonical block of a stored matrix**: `rows × cols` entries of `width` words from
offset `off` of buffer `b`, of length `rows * cols * width`. Kernel and routine specifications
state their footprints in this form, so that equal blocks are syntactically equal and the
lengths of different statements (`2 * (r * k)`, `k * r * 2`) need no rewriting. -/
def matBlock (b off rows cols width : ℕ) : ℕ × ℕ × ℕ := (b, off, rows * cols * width)

/-- Blocks in different buffers are disjoint. -/
theorem blockDisjoint_of_fst_ne {x y : ℕ × ℕ × ℕ} (h : x.1 ≠ y.1) :
    blockDisjoint x y = true :=
  blockDisjoint_iff.mpr (Or.inl h)

/-- A block that ends before another starts in the same buffer is disjoint from it: the layout
lemma for blocks packed one after another. -/
theorem blockDisjoint_of_add_le {x y : ℕ × ℕ × ℕ} (h : x.2.1 + x.2.2 ≤ y.2.1) :
    blockDisjoint x y = true :=
  blockDisjoint_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- The length of a matrix block does not depend on the order of its dimensions. -/
theorem matBlock_comm (b off rows cols width : ℕ) :
    matBlock b off rows cols width = (b, off, cols * rows * width) := by
  rw [matBlock, Nat.mul_comm rows cols]

/-- **Scratch on top, dropped**: a run from the store with a buffer pushed, whose footprint
includes a block of the pushed buffer, modifies in the original store, after the pop, only the
blocks below it. -/
theorem Modifies.pop_top {fp : List (ℕ × ℕ × ℕ)} {s s' : Store P K} {y : P × Array (Option K)}
    {o l : ℕ} (h : Modifies (fp ++ [(s.size, o, l)]) (s.push y) s') : Modifies fp s s'.pop := by
  have hsz : s'.size = s.size + 1 := by
    rw [← Store.size_eq_of_shape_eq h.1.symm, Array.size_push]
  refine ⟨?_, fun q b i hb => ?_⟩
  · rw [Store.shape_pop, h.1, Store.shape, Array.map_push, Array.pop_push]
    rfl
  · by_cases hlt : b < s.size
    · rw [Store.read_pop_of_lt (by omega), h.2 q b i fun x hx => ?_,
        Store.read_push_of_ne (by omega)]
      rcases List.mem_append.mp hx with hx | hx
      · exact hb x hx
      · rw [List.mem_singleton.mp hx]
        exact blockDisjoint_of_fst_ne (Nat.ne_of_lt hlt)
    · rw [Store.read_eq_none_of_size_le (by rw [Array.size_pop]; omega),
        Store.read_eq_none_of_size_le (by omega)]

/-- Scratch on top: a run from the store with a buffer pushed, popped at the end, modifies in
the original store only the blocks it modified below the top. -/
theorem Modifies.pop {fp : List (ℕ × ℕ × ℕ)} {s s' : Store P K} {y : P × Array (Option K)}
    (h : Modifies fp (s.push y) s') : Modifies fp s s'.pop :=
  Modifies.pop_top (o := 0) (l := 0) (h.mono fun _ hx => List.mem_append_left _ hx)

/-- A writable block stays writable through any modification (by the shape clause; the frame
rule does not apply to a block that was just written). -/
theorem Writable.of_modifies {p : P} {b off n : ℕ} {fp : List (ℕ × ℕ × ℕ)} {s s' : Store P K}
    (h : Writable s p b off n) (hm : Modifies fp s s') : Writable s' p b off n :=
  h.of_shape_eq hm.1

/-- Writable blocks stay writable through any modification. -/
theorem WritableBlocks.of_modifies {p : P} {bs fp : List (ℕ × ℕ × ℕ)} {s s' : Store P K}
    (h : WritableBlocks s p bs) (hm : Modifies fp s s') : WritableBlocks s' p bs :=
  fun x hx => (h x hx).of_modifies hm

end Footprint

/-! ### Modes, weakest preconditions and triples -/

/-- **The mode of a judgement**: `total` asserts that the run succeeds, `liberal` only constrains
a successful run (Dijkstra's weakest liberal precondition). -/
inductive Mode where
  /-- The run succeeds and its final state satisfies the postcondition. -/
  | total
  /-- If the run succeeds, its final state satisfies the postcondition. -/
  | liberal

/-- What a mode needs of the arithmetic: the total mode needs `A`, the liberal mode nothing. A
specification proved for every mode `m` under `m.Needs A` gives, at `liberal`, the refinement
without `A` and, at `total`, success under `A`, from one proof. -/
def Mode.Needs : Mode → Prop → Prop
  | .total, A => A
  | .liberal, _ => True

/-- The outcome `o` of a step satisfies `Q` in mode `m`. -/
def Mode.Sat {α : Type} : Mode → (α → Prop) → Option α → Prop
  | .total, Q, o => ∃ x, o = some x ∧ Q x
  | .liberal, Q, o => ∀ x, o = some x → Q x

/-- A satisfied outcome satisfies a weaker predicate. -/
theorem Mode.Sat.mono {α : Type} {m : Mode} {Q Q' : α → Prop} {o : Option α}
    (h : m.Sat Q o) (hQ : ∀ x, Q x → Q' x) : m.Sat Q' o := by
  cases m
  · obtain ⟨x, hx, hq⟩ := h
    exact ⟨x, hx, hQ x hq⟩
  · exact fun x hx => hQ x (h x hx)

/-- A successful outcome satisfies `Q` iff its value does. -/
theorem Mode.sat_some {α : Type} {m : Mode} {Q : α → Prop} {x : α} :
    m.Sat Q (some x) ↔ Q x := by
  cases m <;> simp [Mode.Sat]

/-- An outcome in sequence: the bind of the outcome monad. -/
theorem Mode.sat_bind {α β : Type} {m : Mode} {Q : β → Prop} {o : Option α}
    {f : α → Option β} : m.Sat Q (o.bind f) ↔ m.Sat (fun x => m.Sat Q (f x)) o := by
  cases m <;> cases o <;> simp [Mode.Sat]

/-- An outcome mapped. -/
theorem Mode.sat_map {α β : Type} {m : Mode} {Q : β → Prop} {o : Option α} {f : α → β} :
    m.Sat Q (o.map f) ↔ m.Sat (fun x => Q (f x)) o := by
  cases m <;> cases o <;> simp [Mode.Sat]

/-- A requirement of the total mode holds in the liberal mode. -/
theorem Mode.needs_liberal (A : Prop) : Mode.liberal.Needs A := trivial

/-- A requirement that holds holds in every mode. -/
theorem Mode.needs_of {A : Prop} (h : A) (m : Mode) : m.Needs A := by
  cases m
  · exact h
  · trivial

/-- A requirement of a conjunction is the conjunction of the requirements. -/
theorem Mode.needs_and {m : Mode} {A B : Prop} : m.Needs (A ∧ B) ↔ m.Needs A ∧ m.Needs B := by
  cases m
  · exact Iff.rfl
  · exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

/-- A requirement implies its consequences. -/
theorem Mode.Needs.mono {m : Mode} {A B : Prop} (h : A → B) (hA : m.Needs A) : m.Needs B := by
  cases m
  · exact h hA
  · trivial

/-- A requirement used to establish another. -/
theorem Mode.Needs.elim {m : Mode} {A B : Prop} (hA : m.Needs A) (h : A → m.Needs B) :
    m.Needs B := by
  cases m
  · exact h hA
  · trivial

omit [DecidableEq P] in
/-- A state whose tape positions are those of another. -/
def PosKept {C : Type} (st st' : St P K C) : Prop := st'.pos = st.pos

variable [AddMonoid C]

/-- A state with its count raised by `c`: the state after a charged step that writes nothing. -/
def St.addCnt (st : St P K C) (c : C) : St P K C := { st with cnt := st.cnt + c }

/-- **The weakest precondition** of `s` for `Q` in mode `m`: the run of `s` from `st` under `I`
ends (`total`: succeeds and ends; `liberal`: if it succeeds, ends) in a state satisfying `Q`. -/
def Wp (m : Mode) (I : Interp P ι K C) (s : Stmt P ι ℕ ℕ) (Q : St P K C → Prop)
    (st : St P K C) : Prop :=
  m.Sat Q (exec I s st)

/-- **A triple** in mode `m`: from every state satisfying `pre`, the run of `s` ends in a state
related to the start by `post`. -/
def Triple (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop) (s : Stmt P ι ℕ ℕ)
    (post : St P K C → St P K C → Prop) : Prop :=
  ∀ st, pre st → Wp m I s (post st) st

section Core

variable {m : Mode} {I : Interp P ι K C} {s t : Stmt P ι ℕ ℕ} {Q Q' : St P K C → Prop}
  {st : St P K C}

/-- The weakest precondition is monotone in the postcondition. -/
theorem wp_mono (h : Wp m I s Q st) (hQ : ∀ st', Q st' → Q' st') : Wp m I s Q' st :=
  Mode.Sat.mono h hQ

/-- **The application rule**: a triple gives the weakest precondition of any postcondition its
own implies, at a state satisfying its precondition. -/
theorem Triple.wp_of {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple m I pre s post) (hpre : pre st) (hQ : ∀ st', post st st' → Q st') :
    Wp m I s Q st :=
  wp_mono (h st hpre) hQ

/-- **The rule of consequence.** -/
theorem Triple.conseq {pre pre' : St P K C → Prop} {post post' : St P K C → St P K C → Prop}
    (h : Triple m I pre s post) (hpre : ∀ st, pre' st → pre st)
    (hpost : ∀ st st', pre' st → post st st' → post' st st') : Triple m I pre' s post' :=
  fun st hst => wp_mono (h st (hpre st hst)) fun st' hp => hpost st st' hst hp

/-- A total triple is a liberal one. -/
theorem Triple.liberal {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple .total I pre s post) : Triple .liberal I pre s post := by
  intro st hst x hx
  obtain ⟨y, hy, hq⟩ := h st hst
  rw [hy] at hx
  cases hx
  exact hq

/-- A liberal triple and success give a total triple (the run is deterministic). -/
theorem Triple.total_of_liberal {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple .liberal I pre s post) (hs : ∀ st, pre st → ∃ st', exec I s st = some st') :
    Triple .total I pre s post := by
  intro st hst
  obtain ⟨st', hs⟩ := hs st hst
  exact ⟨st', hs, h st hst st' hs⟩

/-- A total triple: the run succeeds. -/
theorem Triple.exists_exec {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple .total I pre s post) (hpre : pre st) :
    ∃ st', exec I s st = some st' ∧ post st st' :=
  h st hpre

/-- A liberal triple: what a successful run satisfies. -/
theorem Triple.holds_of_exec {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    {st' : St P K C} (h : Triple .liberal I pre s post) (hpre : pre st)
    (hrun : exec I s st = some st') : post st st' :=
  h st hpre st' hrun

/-! #### Statement rules -/

/-- `skip`. -/
theorem wp_skip : Wp m I .skip Q st ↔ Q st := by
  rw [Wp, exec_skip, Mode.sat_some]

/-- **Sequence**: the weakest precondition of `t` is the postcondition of `s`. -/
theorem wp_seq : Wp m I (.seq s t) Q st ↔ Wp m I s (Wp m I t Q) st := by
  rw [Wp, exec_seq, Mode.sat_bind]
  rfl

/-- A scalar instruction. -/
theorem wp_instr (i : Instr P ℕ ℕ) :
    Wp m I (.instr i) Q st ↔
      m.Sat (fun r => Q ({ st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i.kind }))
        (i.run I.sem I.tape st.store st.pos) := by
  rw [Wp, exec_instr, Mode.sat_map]

/-- **Allocation**: the body runs from the state with the fresh buffer at handle
`st.store.size`, and the postcondition is read after its release. -/
theorem wp_alloc (p : P) (len : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ) :
    Wp m I (.alloc p len body) Q st ↔
      Wp m I (body st.store.size) (fun st₂ => Q (st₂.release p len.eval (I.width p)))
        (st.allocate p len.eval (I.width p)) := by
  rw [Wp, exec_alloc, Mode.sat_map]
  rfl

/-- **A conditional**, from the comparison step. -/
theorem wp_ite (p : P) (c : CmpOp) (x y : Cell ℕ ℕ) :
    Wp m I (.ite p c x y s t) Q st ↔
      m.Sat (fun r => if r.1 then Wp m I s Q r.2 else Wp m I t Q r.2) (cmpStep I p c x y st) := by
  rw [Wp, exec_ite, Mode.sat_bind]
  refine iff_of_eq (congrArg (m.Sat · _) (funext fun r => ?_))
  split <;> rfl

/-- A conditional on stored values: with the cells read and compared, the branch taken. -/
theorem wp_ite_of_read {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {a b : K} {r : Bool}
    (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some b) (hr : I.sem.cmp p c a b = some r) :
    Wp m I (.ite p c x y s t) Q st ↔
      if r then Wp m I s Q (st.addCnt (I.charge (.cmp p)))
      else Wp m I t Q (st.addCnt (I.charge (.cmp p))) := by
  rw [wp_ite]
  simp only [cmpStep, hx, hy, hr, Option.bind_some, Option.map_some, Mode.sat_some]
  rfl

/-- **An index binder** on a stored value: the body runs at every converted value $k$ with the
fact $k \le \mathit{bound}$; the total mode needs the bound. -/
theorem wp_bindIdx_of_read {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {v : K} (hx : st.store.read p x.buf x.idx.eval = some v)
    (h : m.Sat (fun k => m.Needs (k ≤ bound.eval) ∧
      (k ≤ bound.eval → Wp m I (body k) Q (st.addCnt (I.charge (.toNat p)))))
      (I.sem.toNat p v)) :
    Wp m I (.bindIdx p x bound body) Q st := by
  rw [Wp, exec_bindIdx, toNatStep, hx, Option.bind_some]
  cases hk : I.sem.toNat p v with
  | none =>
    rw [hk] at h
    cases m
    · obtain ⟨_, h, _⟩ := h
      cases h
    · intro x hx
      cases hx
  | some k =>
    rw [hk, Mode.sat_some] at h
    rw [Option.map_some, Option.bind_some]
    dsimp only
    split_ifs with hkb
    · exact h.2 hkb
    · cases m
      · exact absurd h.1 hkb
      · intro x hx
        cases hx

/-- **A kernel call**: the black box's store, charged once. -/
theorem wp_kcall (o : ι) (p : P) (dims : List (IExp ℕ)) (ins outs : List (ℕ × IExp ℕ)) :
    Wp m I (.kcall o p dims ins outs) Q st ↔
      m.Sat (fun s => Q ({ st with store := s } |>.addCnt
          (I.charge (.kcall p o (dims.map IExp.eval)))))
        (I.kcallStore o p (dims.map IExp.eval) (ins.map fun x => (x.1, x.2.eval))
          (outs.map fun x => (x.1, x.2.eval)) st.store) := by
  rw [Wp, exec_kcall, Mode.sat_map]
  rfl

/-- A named kernel runs as its body (the label is transparent to the logic). -/
theorem wp_named (name : String) (args : List (Arg ℕ ℕ)) :
    Wp m I (.named name args s) Q st ↔ Wp m I s Q st := by
  rw [Wp, exec_named, Wp]

/-! #### Composite rules -/

/-- **Sequence of triples**: the first routine's output feeds the second (`hmid`), and the
composite postcondition names the intermediate state. -/
theorem Triple.seq {pre pre₂ : St P K C → Prop} {mid post : St P K C → St P K C → Prop}
    (h₁ : Triple m I pre s mid) (h₂ : Triple m I pre₂ t post)
    (hmid : ∀ st st₁, pre st → mid st st₁ → pre₂ st₁) :
    Triple m I pre (.seq s t) fun st st₂ => ∃ st₁, mid st st₁ ∧ post st₁ st₂ :=
  fun st hst => (wp_seq).mpr <| wp_mono (h₁ st hst) fun st₁ hmid₁ =>
    wp_mono (h₂ st₁ (hmid st st₁ hst hmid₁)) fun _ hp => ⟨st₁, hmid₁, hp⟩

omit [DecidableEq P] [AddMonoid C] in
/-- A fold over the indices below $i + 1$ is the fold below $i$, then step $i$. -/
private theorem foldlM_range_succ_eq_bind {α : Type} (f : α → ℕ → Option α) (a : α) (i : ℕ) :
    (List.range (i + 1)).foldlM f a = ((List.range i).foldlM f a).bind fun r => f r i := by
  rw [List.range_succ, List.foldlM_append]
  cases (List.range i).foldlM f a with
  | none => rfl
  | some r =>
    change ([i].foldlM f r) = f r i
    simp only [List.foldlM_cons, List.foldlM_nil]
    cases f r i <;> rfl

omit [DecidableEq P] [AddMonoid C] in
/-- A satisfied outcome is also an outcome that occurred. -/
theorem Mode.Sat.and_eq {α : Type} {m : Mode} {Q : α → Prop} {o : Option α} (h : m.Sat Q o) :
    m.Sat (fun x => o = some x ∧ Q x) o := by
  cases m
  · obtain ⟨x, hx, hq⟩ := h
    exact ⟨x, hx, hx, hq⟩
  · exact fun x hx => ⟨hx, h x hx⟩

/-- **A loop with an invariant**: `Inv st₀ k` holds of the state after `k` iterations from
`st₀`, and the body keeps it. -/
theorem Triple.loop {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {pre : St P K C → Prop}
    (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Triple m I (Inv st₀ k) (body k) fun _ st' => Inv st₀ (k + 1) st') :
    Triple m I pre (.loop n body) fun st₀ st' => Inv st₀ n.eval st' := by
  intro st₀ hst
  rw [Wp, exec_loop]
  suffices ∀ j ≤ n.eval, m.Sat (Inv st₀ j)
      ((List.range j).foldlM (fun st i => exec I (body i) st) st₀) from this _ le_rfl
  intro j
  induction j with
  | zero => exact fun _ => Mode.sat_some.mpr (h0 st₀ hst)
  | succ j ih =>
    intro hj
    rw [foldlM_range_succ_eq_bind, Mode.sat_bind]
    exact (ih (by omega)).mono fun st₁ h₁ => hstep st₀ hst j (by omega) st₁ h₁

/-- **A fueled loop with an invariant**: `Inv st₀ j` holds of the state before the $j$-th test;
a test that holds runs the body to `Inv st₀ (j + 1)`, and in the total mode leaves fuel for the
next test. The final state is the state of a failed test. -/
theorem Triple.whileFuel {fuel : IExp ℕ} {p : P} {c : CmpOp} {x y : Cell ℕ ℕ}
    {body : Stmt P ι ℕ ℕ} {pre : St P K C → Prop} (Inv : St P K C → ℕ → St P K C → Prop)
    (h0 : ∀ st, pre st → m.Needs (0 < fuel.eval) ∧ Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ j st, Inv st₀ j st →
      m.Sat (fun r => r.1 = true → m.Needs (j + 1 < fuel.eval) ∧
        Wp m I body (Inv st₀ (j + 1)) r.2) (cmpStep I p c x y st)) :
    Triple m I pre (.whileFuel fuel p c x y body) fun st₀ st' =>
      ∃ j stj, Inv st₀ j stj ∧ cmpStep I p c x y stj = some (false, st') := by
  intro st₀ hst
  let Post : St P K C → Prop := fun st' =>
    ∃ j stj, Inv st₀ j stj ∧ cmpStep I p c x y stj = some (false, st')
  let R : ℕ → St P K C × Bool → Prop := fun i r =>
    (r.2 = true → Inv st₀ i r.1 ∧ m.Needs (i < fuel.eval)) ∧ (r.2 = false → Post r.1)
  have hfold : ∀ i ≤ fuel.eval, m.Sat (R i) ((List.range i).foldlM (fun (s : St P K C × Bool) _ =>
      if s.2 then (cmpStep I p c x y s.1).bind fun r =>
        if r.1 then (exec I body r.2).map fun st' => (st', true) else some (r.2, false)
      else some s) (st₀, true)) := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨hf, h0'⟩ := h0 st₀ hst
      exact Mode.sat_some.mpr ⟨fun _ => ⟨h0', hf⟩, fun h => absurd h (by simp)⟩
    | succ i ih =>
      intro hi
      rw [foldlM_range_succ_eq_bind, Mode.sat_bind]
      refine (ih (by omega)).mono fun ⟨s, b⟩ ⟨hT, hF⟩ => ?_
      cases b with
      | false => exact Mode.sat_some.mpr ⟨fun h => absurd h (by simp), hF⟩
      | true =>
        obtain ⟨hinv, -⟩ := hT rfl
        rw [if_pos rfl, Mode.sat_bind]
        refine (hstep st₀ hst i s hinv).and_eq.mono fun ⟨r, s'⟩ ⟨heq, hr⟩ => ?_
        cases r with
        | false => exact Mode.sat_some.mpr ⟨fun h => absurd h (by simp), fun _ => ⟨i, s, hinv, heq⟩⟩
        | true =>
          obtain ⟨hneeds, hwp⟩ := hr rfl
          rw [if_pos rfl, Mode.sat_map]
          exact Mode.Sat.mono hwp fun st' h' => ⟨fun _ => ⟨h', hneeds⟩, fun h => absurd h (by simp)⟩
  rw [Wp, exec, Mode.sat_bind]
  refine (hfold _ le_rfl).mono fun ⟨s, b⟩ ⟨hT, hF⟩ => ?_
  cases b with
  | false => exact Mode.sat_some.mpr (hF rfl)
  | true =>
    cases m
    · exact absurd (hT rfl).2 (lt_irrefl _)
    · intro _ h
      cases h

/-- **Scoped scratch**: a body that runs from the state with the fresh buffer at the relative
handle `b` (the size of the store, fixed by the precondition) gives the allocation, its
postcondition read after the release. -/
theorem Triple.alloc {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {b : ℕ}
    {pre pre' : St P K C → Prop} {post post' : St P K C → St P K C → Prop}
    (h : Triple m I pre' (body b) post') (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st, pre st → pre' (st.allocate p len.eval (I.width p)))
    (hpost : ∀ st st₂, pre st → post' (st.allocate p len.eval (I.width p)) st₂ →
      post st (st₂.release p len.eval (I.width p))) :
    Triple m I pre (.alloc p len body) post := by
  intro st hst
  rw [wp_alloc, hb st hst]
  exact wp_mono (h _ (hpre st hst)) fun st₂ hp => hpost st st₂ hst hp

omit [AddMonoid C] in
/-- The allocated state has one buffer more. -/
theorem St.size_allocate (st : St P K C) (p : P) (len w : ℕ) :
    (st.allocate p len w).store.size = st.store.size + 1 := by
  simp [St.allocate]

omit [AddMonoid C] in
/-- The fresh buffer is writable on its whole length, at its relative handle. -/
theorem St.writable_allocate (st : St P K C) (p : P) (len w : ℕ) :
    Writable (st.allocate p len w).store p st.store.size 0 len := by
  intro i hi
  refine ⟨len, ?_, by omega⟩
  rw [St.shape_allocate, Array.getElem?_push, if_pos (Store.size_shape _).symm]

omit [AddMonoid C] in
/-- Releasing the top buffer keeps every read below it. -/
theorem St.read_release_of_lt (st : St P K C) (p : P) (len w : ℕ) (q : P) {b : ℕ}
    (hb : b + 1 < st.store.size) (i : ℕ) :
    (st.release p len w).store.read q b i = st.store.read q b i :=
  Store.read_pop_of_lt (by omega)

end Core

/-! ### Builders -/

section Builder

variable {m : Mode} {I : Interp P ι K C} {Q : St P K C → Prop} {st : St P K C}

/-- **A builder in sequence**: a composable prefix, then the rest. -/
theorem wp_run_bind {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    (hx : ExecutionComposable I x) :
    Wp m I (x >>= f).run Q st ↔ Wp m I x.run (Wp m I (f ()).run Q) st := by
  rw [Wp, hx f st, Mode.sat_bind]
  rfl

/-- **An allocation in a builder**: the rest of the block runs on the fresh handle. -/
theorem wp_run_allocBind {p : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} :
    Wp m I (Builder.alloc p len >>= f).run Q st ↔
      Wp m I (f st.store.size).run (fun st₂ => Q (st₂.release p len.eval (I.width p)))
        (st.allocate p len.eval (I.width p)) :=
  wp_alloc p len fun b => (f b).run

/-- The empty builder. -/
theorem wp_run_pure : Wp m I (pure () : Builder P ι ℕ ℕ Unit).run Q st ↔ Q st :=
  wp_skip

/-- A statement is a composable prefix. -/
theorem executionComposable_stmt (s : Stmt P ι ℕ ℕ) :
    ExecutionComposable I (Builder.stmt s) :=
  executionComposable_single I fun _ => rfl

/-- A scalar instruction is a composable prefix. -/
theorem executionComposable_ins (i : Instr P ℕ ℕ) :
    ExecutionComposable I (Builder.ins (ι := ι) i) :=
  executionComposable_single I fun _ => rfl

/-- A scope is a composable prefix. -/
theorem executionComposable_scope (x : Builder P ι ℕ ℕ Unit) :
    ExecutionComposable I (Builder.scope x) :=
  executionComposable_single I fun _ => rfl

/-- A named kernel is a composable prefix. -/
theorem executionComposable_named (name : String) (args : List (Arg ℕ ℕ))
    (x : Builder P ι ℕ ℕ Unit) : ExecutionComposable I (Builder.named name args x) :=
  executionComposable_single I fun _ => rfl

/-- A loop is a composable prefix. -/
theorem executionComposable_forRange (n : IExp ℕ) (body : ℕ → Builder P ι ℕ ℕ Unit) :
    ExecutionComposable I (Builder.forRange n body) :=
  executionComposable_single I fun _ => rfl

/-- A conditional is a composable prefix. -/
theorem executionComposable_ifThenElse (p : P) (c : CmpOp) (x y : Cell ℕ ℕ)
    (t e : Builder P ι ℕ ℕ Unit) : ExecutionComposable I (Builder.ifThenElse p c x y t e) :=
  executionComposable_single I fun _ => rfl

/-- An index binder is a composable prefix. -/
theorem executionComposable_bindIdx (p : P) (x : Cell ℕ ℕ) (bound : IExp ℕ)
    (body : ℕ → Builder P ι ℕ ℕ Unit) :
    ExecutionComposable I (Builder.bindIdx p x bound body) :=
  executionComposable_single I fun _ => rfl

end Builder

/-! ### Routine specifications -/

section Spec

/-- **A routine specification**: a triple whose postcondition also bounds what the run modifies
to the blocks `fp`. Inputs, outputs and scratch are blocks of the footprint or of the
precondition's read sets, so frames and disjointness are linear arithmetic on their offsets. -/
def Spec (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop) (s : Stmt P ι ℕ ℕ)
    (fp : List (ℕ × ℕ × ℕ)) (post : St P K C → St P K C → Prop) : Prop :=
  Triple m I pre s fun st st' => Modifies fp st.store st'.store ∧ post st st'

/-- **A specified routine**: a builder that composes with what follows and whose run meets a
specification. The analogue of `NLAlib.Computation.IsBlockRoutine` with a postcondition. -/
structure RoutineSpec (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop)
    (r : Builder P ι ℕ ℕ Unit) (fp : List (ℕ × ℕ × ℕ)) (post : St P K C → St P K C → Prop) :
    Prop where
  /-- The routine composes with the following program. -/
  composable : ExecutionComposable I r
  /-- Its run meets the specification. -/
  spec : Spec m I pre r.run fp post

variable {m : Mode} {I : Interp P ι K C} {s t : Stmt P ι ℕ ℕ} {st : St P K C}
  {pre pre₂ : St P K C → Prop} {post post₂ : St P K C → St P K C → Prop}
  {fp fp₂ : List (ℕ × ℕ × ℕ)}

/-- Consequence for specifications, with a larger footprint. -/
theorem Spec.conseq {pre' : St P K C → Prop} {post' : St P K C → St P K C → Prop}
    {fp' : List (ℕ × ℕ × ℕ)} (h : Spec m I pre s fp post) (hpre : ∀ st, pre' st → pre st)
    (hfp : ∀ x ∈ fp, x ∈ fp') (hpost : ∀ st st', pre' st → post st st' → post' st st') :
    Spec m I pre' s fp' post' :=
  Triple.conseq h hpre fun st st' hst hp => ⟨hp.1.mono hfp, hpost st st' hst hp.2⟩

/-- **Sequence of specifications**: footprints add, the first output feeds the second. -/
theorem Spec.seq (h₁ : Spec m I pre s fp post) (h₂ : Spec m I pre₂ t fp₂ post₂)
    (hmid : ∀ st st₁, pre st → Modifies fp st.store st₁.store → post st st₁ → pre₂ st₁) :
    Spec m I pre (.seq s t) (fp ++ fp₂) fun st st₂ => ∃ st₁, post st st₁ ∧ post₂ st₁ st₂ :=
  Triple.conseq (Triple.seq h₁ h₂ fun st st₁ hst hp => hmid st st₁ hst hp.1 hp.2) (fun _ h => h)
    fun _ _ _ ⟨st₁, ⟨hm₁, hp₁⟩, hm₂, hp₂⟩ => ⟨hm₁.trans hm₂, st₁, hp₁, hp₂⟩

/-- **The frame rule**: a predicate reading only blocks disjoint from the footprint is kept. -/
theorem Spec.frame {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} (h : Spec m I pre s fp post)
    (hF : ReadsOnly F rs) (hd : BlocksDisjoint rs fp) :
    Spec m I (fun st => pre st ∧ F st.store) s fp fun st st' => post st st' ∧ F st'.store :=
  fun st hst => wp_mono (h st hst.1) fun _ hp => ⟨hp.1, hp.2, hF.of_modifies hst.2 hp.1 hd⟩

omit [AddMonoid C] in
/-- The frame of one step of a proof: what a specified step keeps. -/
theorem ReadsOnly.of_spec_post {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {st' : St P K C}
    (hF : ReadsOnly F rs) (h : F st.store) (hm : Modifies fp st.store st'.store)
    (hd : BlocksDisjoint rs fp) : F st'.store :=
  hF.of_modifies h hm hd

/-- **A conditional of specifications** on a comparison whose outcome `r` the precondition
fixes. -/
theorem Spec.ite {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {r : Bool}
    {preT preE : St P K C → Prop} {postT postE : St P K C → St P K C → Prop}
    (ht : Spec m I preT s fp postT) (he : Spec m I preE t fp postE)
    (hcmp : ∀ st, pre st → ∃ a b, st.store.read p x.buf x.idx.eval = some a ∧
      st.store.read p y.buf y.idx.eval = some b ∧ I.sem.cmp p c a b = some r)
    (hT : ∀ st, pre st → r = true → preT (st.addCnt (I.charge (.cmp p))))
    (hE : ∀ st, pre st → r = false → preE (st.addCnt (I.charge (.cmp p)))) :
    Spec m I pre (.ite p c x y s t) fp fun st st' =>
      (r = true → postT (st.addCnt (I.charge (.cmp p))) st') ∧
        (r = false → postE (st.addCnt (I.charge (.cmp p))) st') := by
  intro st hst
  obtain ⟨a, b, hx, hy, hr⟩ := hcmp st hst
  rw [wp_ite_of_read hx hy hr]
  cases r
  · exact wp_mono (he _ (hE st hst rfl)) fun _ hp =>
      ⟨hp.1, fun h => absurd h (by simp), fun _ => hp.2⟩
  · exact wp_mono (ht _ (hT st hst rfl)) fun _ hp =>
      ⟨hp.1, fun _ => hp.2, fun h => absurd h (by simp)⟩

/-- **A loop of specifications** with an invariant and one footprint for every iteration. -/
theorem Spec.loop {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Spec m I (Inv st₀ k) (body k) fp fun _ st' => Inv st₀ (k + 1) st') :
    Spec m I pre (.loop n body) fp fun st₀ st' => Inv st₀ n.eval st' := by
  refine Triple.conseq (Triple.loop (fun st₀ k st => Inv st₀ k st ∧ Modifies fp st₀.store st.store)
    (fun st hst => ⟨h0 st hst, Modifies.refl _ _⟩) fun st₀ hst k hk => ?_) (fun _ h => h)
    fun _ _ _ hp => ⟨hp.2, hp.1⟩
  exact fun st hp => wp_mono (hstep st₀ hst k hk st hp.1) fun _ hq =>
    ⟨hq.2, (hp.2.trans hq.1).mono fun x hx => by
      rcases List.mem_append.mp hx with hx | hx <;> exact hx⟩

/-- **Scoped scratch for specifications**: the body may modify the fresh buffer at the relative
handle `b`; the allocation's footprint is the body's below it. -/
theorem Spec.alloc {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {b : ℕ}
    {pre' : St P K C → Prop} {post' : St P K C → St P K C → Prop}
    (h : Spec m I pre' (body b) (fp ++ [(b, 0, len.eval)]) post')
    (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st, pre st → pre' (st.allocate p len.eval (I.width p)))
    (hpost : ∀ st st₂, pre st → post' (st.allocate p len.eval (I.width p)) st₂ →
      post st (st₂.release p len.eval (I.width p))) :
    Spec m I pre (.alloc p len body) fp post := by
  refine Triple.alloc h hb hpre fun st st₂ hst hp => ⟨?_, hpost st st₂ hst hp.2⟩
  have hm := hp.1
  rw [← hb st hst] at hm
  exact Modifies.pop_top hm

/-- **The call rule**: a specified routine followed by the rest of a builder, without unfolding
the routine; the rest starts from a named state with the routine's effect as hypotheses. -/
theorem RoutineSpec.wp_bind {r : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    {Q : St P K C → Prop} (h : RoutineSpec m I pre r fp post) (hpre : pre st)
    (hk : ∀ st', Modifies fp st.store st'.store → post st st' → Wp m I (f ()).run Q st') :
    Wp m I (r >>= f).run Q st := by
  rw [wp_run_bind h.composable]
  exact h.spec.wp_of hpre fun st' hp => hk st' hp.1 hp.2

/-- The call rule for the last routine of a block. -/
theorem RoutineSpec.wp_run {r : Builder P ι ℕ ℕ Unit} {Q : St P K C → Prop}
    (h : RoutineSpec m I pre r fp post) (hpre : pre st)
    (hk : ∀ st', Modifies fp st.store st'.store → post st st' → Q st') :
    Wp m I r.run Q st :=
  h.spec.wp_of hpre fun st' hp => hk st' hp.1 hp.2

/-- Two specified routines in sequence form one. -/
theorem RoutineSpec.bind {r₁ r₂ : Builder P ι ℕ ℕ Unit} (h₁ : RoutineSpec m I pre r₁ fp post)
    (h₂ : RoutineSpec m I pre₂ r₂ fp₂ post₂)
    (hmid : ∀ st st₁, pre st → Modifies fp st.store st₁.store → post st st₁ → pre₂ st₁) :
    RoutineSpec m I pre (r₁ >>= fun _ => r₂) (fp ++ fp₂)
      fun st st₂ => ∃ st₁, post st st₁ ∧ post₂ st₁ st₂ := by
  refine ⟨h₁.composable.bind h₂.composable, fun st hst => ?_⟩
  refine h₁.wp_bind hst fun st₁ hm₁ hp₁ => ?_
  exact h₂.spec.wp_of (hmid st st₁ hst hm₁ hp₁) fun st₂ hp₂ => ⟨hm₁.trans hp₂.1, st₁, hp₁, hp₂.2⟩

/-- A scope around a specified routine is specified alike. -/
theorem RoutineSpec.scope {r : Builder P ι ℕ ℕ Unit} (h : Spec m I pre r.run fp post) :
    RoutineSpec m I pre (Builder.scope r) fp post :=
  ⟨executionComposable_scope r, fun st hst => (wp_seq).mpr <|
    wp_mono (h st hst) fun _ hp => (wp_skip).mpr hp⟩

/-- **A specification from a liberal one and success**, each from its own proof. -/
theorem Spec.total_of_liberal (h : Spec .liberal I pre s fp post)
    (hs : ∀ st, pre st → ∃ st', exec I s st = some st') : Spec .total I pre s fp post :=
  Triple.total_of_liberal h hs

/-- **A statement step as a routine**: the call rule applies to `Builder.stmt s` (a kernel call
in a builder) with the specification of `s`. -/
theorem RoutineSpec.stmt (h : Spec m I pre s fp post) :
    RoutineSpec m I pre (Builder.stmt s) fp post :=
  ⟨executionComposable_stmt s, fun st hst => (wp_seq).mpr <|
    wp_mono (h st hst) fun _ hp => (wp_skip).mpr hp⟩

/-- A scalar instruction step as a routine. -/
theorem RoutineSpec.ins {i : Instr P ℕ ℕ} (h : Spec m I pre (.instr i) fp post) :
    RoutineSpec m I pre (Builder.ins i) fp post :=
  RoutineSpec.stmt h

/-- **Transport across run equivalence**: a specified routine specifies every composable builder
whose run runs the same (index normal forms, `Builder` rewrites). -/
theorem RoutineSpec.congr {r r' : Builder P ι ℕ ℕ Unit} (h : RoutineSpec m I pre r fp post)
    (hc : ExecutionComposable I r') (he : ∀ st, exec I r'.run st = exec I r.run st) :
    RoutineSpec m I pre r' fp post := by
  refine ⟨hc, fun st hst => ?_⟩
  have := h.spec st hst
  rw [Wp, he]
  exact this

/-- A specification transported to a statement of the same index normal form
(`NLAlib.Computation.exec_eq_of_normIdx_eq`). -/
theorem Spec.of_normIdx_eq {s' : Stmt P ι ℕ ℕ} (h : Spec m I pre s fp post)
    (hn : s'.normIdx = s.normIdx) : Spec m I pre s' fp post := by
  intro st hst
  have := h st hst
  rw [Wp, exec_eq_of_normIdx_eq I hn]
  exact this

/-- **An allocation in a builder, by named states**: the rest of the block, specified at the
relative handle `b` from the allocated state `st₁` (an equation, not a pushed term), gives the
block's specification; its footprint below the fresh buffer is the body's. -/
theorem Spec.allocBind {p : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {b : ℕ}
    {pre' : St P K C → Prop} {post' : St P K C → St P K C → Prop}
    (h : Spec m I pre' (f b).run (fp ++ [(b, 0, len.eval)]) post')
    (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st st₁, pre st → st₁ = st.allocate p len.eval (I.width p) → pre' st₁)
    (hpost : ∀ st st₁ st₂, pre st → st₁ = st.allocate p len.eval (I.width p) → post' st₁ st₂ →
      post st (st₂.release p len.eval (I.width p))) :
    Spec m I pre (Builder.alloc p len >>= f).run fp post :=
  Spec.alloc (body := fun b => (f b).run) h hb (fun st hst => hpre st _ hst rfl)
    fun st st₂ hst hp => hpost st _ st₂ hst rfl hp

/-- **A loop with per-iteration footprints**: iteration `k` may modify the blocks `fp k` (which
may depend on ghost sizes read before the loop); the loop modifies their union. -/
theorem Spec.loopFp {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} (fp : ℕ → List (ℕ × ℕ × ℕ))
    (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Spec m I (Inv st₀ k) (body k) (fp k) fun _ st' => Inv st₀ (k + 1) st') :
    Spec m I pre (.loop n body) ((List.range n.eval).flatMap fp)
      fun st₀ st' => Inv st₀ n.eval st' := by
  refine Triple.conseq (Triple.loop (fun st₀ k st => Inv st₀ k st ∧
      Modifies ((List.range k).flatMap fp) st₀.store st.store)
    (fun st hst => ⟨h0 st hst, Modifies.refl _ _⟩) fun st₀ hst k hk => ?_) (fun _ h => h)
    fun _ _ _ hp => ⟨hp.2, hp.1⟩
  refine fun st hp => wp_mono (hstep st₀ hst k hk st hp.1) fun _ hq => ⟨hq.2, ?_⟩
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  exact hp.2.trans hq.1

/-- A loop in a builder, with per-iteration footprints. -/
theorem RoutineSpec.forRange {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit}
    (fp : ℕ → List (ℕ × ℕ × ℕ)) (Inv : St P K C → ℕ → St P K C → Prop)
    (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Spec m I (Inv st₀ k) (body k).run (fp k) fun _ st' => Inv st₀ (k + 1) st') :
    RoutineSpec m I pre (Builder.forRange n body) ((List.range n.eval).flatMap fp)
      fun st₀ st' => Inv st₀ n.eval st' :=
  RoutineSpec.stmt (s := .loop n fun i => (body i).run) (Spec.loopFp fp Inv h0 hstep)

/-- **An index binder of specifications**: the precondition fixes the stored value `v`, which
converts to `k`; the body is specified at `k` with the fact `k ≤ bound` and may have a footprint
depending on `k`; the binder's postcondition records `k ≤ bound`, which the total mode needs. -/
theorem Spec.bindIdx_of_read {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {v : K} {k : ℕ} {pre' : St P K C → Prop} {post' : St P K C → St P K C → Prop}
    (hx : ∀ st, pre st → st.store.read p x.buf x.idx.eval = some v)
    (hk : I.sem.toNat p v = some k) (hbound : m.Needs (k ≤ bound.eval))
    (h : k ≤ bound.eval → Spec m I pre' (body k) fp post')
    (hpre : ∀ st, pre st → pre' (st.addCnt (I.charge (.toNat p)))) :
    Spec m I pre (.bindIdx p x bound body) fp
      fun st st' => k ≤ bound.eval ∧ post' (st.addCnt (I.charge (.toNat p))) st' := by
  intro st hst
  refine wp_bindIdx_of_read (hx st hst) ?_
  rw [hk, Mode.sat_some]
  exact ⟨hbound, fun hkb => wp_mono (h hkb _ (hpre st hst)) fun _ hp => ⟨hp.1, hkb, hp.2⟩⟩

/-- **A two-armed conditional of specifications** (the branch not fixed by the precondition):
the postcondition is that of the arm taken. -/
theorem Spec.ite_cases {p : P} {c : CmpOp} {x y : Cell ℕ ℕ}
    {preT preE : St P K C → Prop} {postT postE : St P K C → St P K C → Prop}
    (ht : Spec m I preT s fp postT) (he : Spec m I preE t fp postE)
    (hcmp : ∀ st, pre st → m.Needs (∃ a b r, st.store.read p x.buf x.idx.eval = some a ∧
      st.store.read p y.buf y.idx.eval = some b ∧ I.sem.cmp p c a b = some r))
    (hT : ∀ st, pre st → preT (st.addCnt (I.charge (.cmp p))))
    (hE : ∀ st, pre st → preE (st.addCnt (I.charge (.cmp p)))) :
    Spec m I pre (.ite p c x y s t) fp fun st st' =>
      postT (st.addCnt (I.charge (.cmp p))) st' ∨ postE (st.addCnt (I.charge (.cmp p))) st' := by
  intro st hst
  rw [wp_ite]
  have hsat : m.Sat (fun r : Bool × St P K C => r.2 = st.addCnt (I.charge (.cmp p)))
      (cmpStep I p c x y st) := by
    have hrun : ∀ r, cmpStep I p c x y st = some r → r.2 = st.addCnt (I.charge (.cmp p)) := by
      intro r hr
      simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨_, _, _, _, _, _, rfl⟩ := hr
      rfl
    cases m
    · obtain ⟨a, b, r, hx, hy, hr⟩ := hcmp st hst
      have he : cmpStep I p c x y st = some (r, st.addCnt (I.charge (.cmp p))) := by
        simp only [cmpStep, hx, hy, hr, Option.bind_some, Option.map_some]
        rfl
      exact ⟨_, he, rfl⟩
    · exact hrun
  refine hsat.mono fun r h₁ => ?_
  obtain ⟨r, st₁⟩ := r
  dsimp only at h₁ ⊢
  subst h₁
  cases r
  · exact wp_mono (he _ (hE st hst)) fun _ hp => ⟨hp.1, Or.inr hp.2⟩
  · exact wp_mono (ht _ (hT st hst)) fun _ hp => ⟨hp.1, Or.inl hp.2⟩

end Spec


/-! ### Counts -/

section Costs

/-- **An exact count**: the final count is the start count plus `c`. Counts thread additively
(`NLAlib.Computation.Costs.trans`) in any additive monoid, and `c` may be a term in the charge
`I.charge`, so one count lemma serves every charge. -/
def Costs (c : C) (st st' : St P K C) : Prop := st'.cnt = st.cnt + c

omit [DecidableEq P] in
/-- No step, no count. -/
theorem Costs.refl (st : St P K C) : Costs 0 st st :=
  (add_zero _).symm

omit [DecidableEq P] in
/-- Counts in sequence add. -/
theorem Costs.trans {c₁ c₂ : C} {st st₁ st₂ : St P K C} (h₁ : Costs c₁ st st₁)
    (h₂ : Costs c₂ st₁ st₂) : Costs (c₁ + c₂) st st₂ := by
  rw [Costs, h₂, h₁, add_assoc]

omit [DecidableEq P] in
/-- A charged step that writes nothing. -/
theorem Costs.addCnt (st : St P K C) (c : C) : Costs c st (st.addCnt c) :=
  rfl

omit [DecidableEq P] in
/-- The counts of a loop add over its iterations. -/
theorem Costs.list_sum {n : ℕ} {c : ℕ → C} {f : ℕ → St P K C}
    (h : ∀ k < n, Costs (c k) (f k) (f (k + 1))) :
    Costs ((List.range n).map c).sum (f 0) (f n) := by
  induction n with
  | zero => exact Costs.refl _
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    exact (ih fun k hk => h k (by omega)).trans (h n (by omega))

/-- **A specification under another charge**, in every mode: success, the store, the tape
positions and the memory of a run do not depend on the charge, so a specification whose
postcondition ignores the count holds under every charge (the run starts from the same state). -/
theorem Spec.withCharge {m : Mode} {I : Interp P ι K C} {pre : St P K C → Prop}
    {s : Stmt P ι ℕ ℕ} {fp : List (ℕ × ℕ × ℕ)} {post : St P K C → St P K C → Prop}
    (ch : OpKind P ι → C) (h : Spec m I pre s fp post)
    (hpost : ∀ st st' c c', post st st' → post { st with cnt := c } { st' with cnt := c' }) :
    Spec m { I with charge := ch } pre s fp post := by
  intro st hst
  cases m
  · obtain ⟨st', hrun, hm, hp⟩ := h st hst
    obtain ⟨c₁, hrun'⟩ := exists_exec_withCharge_eq_some I ch _ hrun st.cnt
    exact ⟨_, hrun', hm, hpost st st' st.cnt c₁ hp⟩
  · intro st' hrun
    obtain ⟨c₁, hrun'⟩ := exists_exec_withCharge_eq_some { I with charge := ch } I.charge _ hrun
      st.cnt
    obtain ⟨hm, hp⟩ := h st hst _ hrun'
    exact ⟨hm, hpost st { st' with cnt := c₁ } st.cnt st'.cnt hp⟩

omit [DecidableEq P] in
/-- **A weighted count bound**: the weight `w` (additive, such as `Finsupp.weight` of a kernel
weight) of the final count exceeds that of the start count by at most `c`. The form of the EP7
weighted kernel count; data-dependent through a supremum over an index binder's values. -/
def CostsLe (w : C →+ ℕ) (c : ℕ) (st st' : St P K C) : Prop := w st'.cnt ≤ w st.cnt + c

omit [DecidableEq P] in
/-- Weighted bounds in sequence add. -/
theorem CostsLe.trans {w : C →+ ℕ} {c₁ c₂ : ℕ} {st st₁ st₂ : St P K C}
    (h₁ : CostsLe w c₁ st st₁) (h₂ : CostsLe w c₂ st₁ st₂) : CostsLe w (c₁ + c₂) st st₂ := by
  unfold CostsLe at *
  omega

omit [DecidableEq P] in
/-- A weighted bound may be raised. -/
theorem CostsLe.mono {w : C →+ ℕ} {c c' : ℕ} {st st' : St P K C} (h : CostsLe w c st st')
    (hc : c ≤ c') : CostsLe w c' st st' := by
  unfold CostsLe at *
  omega

omit [DecidableEq P] in
/-- An exact count gives its weight as a bound. -/
theorem CostsLe.of_costs {w : C →+ ℕ} {c : C} {st st' : St P K C} (h : Costs c st st') :
    CostsLe w (w c) st st' := by
  rw [CostsLe, h, map_add]

omit [DecidableEq P] in
/-- Weighted bounds of a loop add over its iterations. -/
theorem CostsLe.list_sum {w : C →+ ℕ} {n : ℕ} {c : ℕ → ℕ} {f : ℕ → St P K C}
    (h : ∀ k < n, CostsLe w (c k) (f k) (f (k + 1))) :
    CostsLe w ((List.range n).map c).sum (f 0) (f n) := by
  induction n with
  | zero => exact le_add_right le_rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ← add_zero (_ + _)]
    rw [add_zero]
    exact (ih fun k hk => h k (by omega)).trans (h n (by omega))

end Costs

/-! ### Instructions -/

section Instructions

variable {m : Mode} {I : Interp P ι K C} {p : P} {dst x y : Cell ℕ ℕ}

omit [AddMonoid C] in
/-- A scalar write of a writable cell succeeds in the total mode. -/
theorem Mode.sat_write {s : Store P K} {b i : ℕ} {v : K} {Q : Store P K → Prop}
    (hW : m.Needs (Writable s p b i 1)) (hQ : ∀ s', s.write p b i v = some s' → Q s') :
    m.Sat Q (s.write p b i v) := by
  cases m
  · obtain ⟨len, hl, hlt⟩ := hW 0 Nat.one_pos
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape v hl (by omega)
    exact ⟨s', hs', hQ s' hs'⟩
  · exact hQ

/-- **A literal** writes its value into the destination cell, charges one literal and keeps the
tape positions; the total mode needs the cell writable. -/
theorem spec_lit {q : ℚ} {v : K} (hv : I.sem.lit p q = some v) :
    Spec m I (fun st => m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.lit p dst q)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some v ∧ Costs (I.charge (.lit p)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hv, Option.bind_some]
  exact Mode.sat_write hst fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **An index literal**: the value of an index expression as a literal. -/
theorem spec_litIdx {e : IExp ℕ} {v : K} (hv : I.sem.lit p (e.eval : ℚ) = some v) :
    Spec m I (fun st => m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.litIdx p dst e)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some v ∧ Costs (I.charge (.lit p)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hv, Option.bind_some]
  exact Mode.sat_write hst fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **A binary operation** on two stored values. -/
theorem spec_bin {op : BinOp} {a b v : K} (hv : I.sem.bin p op a b = some v) :
    Spec m I (fun st => st.store.read p x.buf x.idx.eval = some a ∧
        st.store.read p y.buf y.idx.eval = some b ∧
        m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.bin p op dst x y)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some v ∧ Costs (I.charge (.bin p op)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hst.1, hst.2.1, hv, Option.bind_some]
  exact Mode.sat_write hst.2.2 fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **A unary operation** on a stored value. -/
theorem spec_un {op : UnOp} {a v : K} (hv : I.sem.un p op a = some v) :
    Spec m I (fun st => st.store.read p x.buf x.idx.eval = some a ∧
        m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.un p op dst x)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some v ∧ Costs (I.charge (.un p op)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hst.1, hv, Option.bind_some]
  exact Mode.sat_write hst.2 fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **A copy** of a stored value. -/
theorem spec_copy {a : K} :
    Spec m I (fun st => st.store.read p x.buf x.idx.eval = some a ∧
        m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.copy p dst x)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some a ∧ Costs (I.charge (.copy p)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hst.1, Option.bind_some]
  exact Mode.sat_write hst.2 fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **A draw** writes the next tape value of its distribution and advances that position. -/
theorem spec_draw {d : Dist} :
    Spec m I (fun st => m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.draw p d dst)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some (I.tape d (st.pos d)) ∧
          Costs (I.charge (.draw p d)) st st' ∧
          st'.pos = Function.update st.pos d (st.pos d + 1) := by
  intro st hst
  rw [Wp, exec_instr, Mode.sat_map, Instr.run, Mode.sat_map]
  exact Mode.sat_write hst fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **A loop of draws** into consecutive cells (`NLAlib.Computation.exec_forRange_draw`): the
block holds the next `n` tape values and the position advances by `n`. -/
theorem spec_forRange_draw (d : Dist) (X off : ℕ) (n : IExp ℕ) (idx : ℕ → IExp ℕ)
    (hidx : ∀ i, (idx i).eval = off + i) :
    RoutineSpec m I (fun st => m.Needs (Writable st.store p X off n.eval))
      (Builder.forRange n fun i => Builder.ins (.draw p d ⟨X, idx i⟩)) [(X, off, n.eval)]
      fun st st' => (∀ i < n.eval, st'.store.read p X (off + i) = some (I.tape d (st.pos d + i))) ∧
        Costs (n.eval • I.charge (.draw p d)) st st' ∧
        st'.pos = Function.update st.pos d (st.pos d + n.eval) := by
  let Inv : St P K C → ℕ → St P K C → Prop := fun st₀ k st =>
    Modifies [(X, off, k)] st₀.store st.store ∧
      (∀ i < k, st.store.read p X (off + i) = some (I.tape d (st₀.pos d + i))) ∧
      Costs (k • I.charge (.draw p d)) st₀ st ∧
      st.pos = Function.update st₀.pos d (st₀.pos d + k)
  refine RoutineSpec.stmt (s := .loop n fun i => (Builder.ins (.draw p d ⟨X, idx i⟩)).run)
    (Triple.conseq (Triple.loop Inv (fun st _ => ⟨?_, fun i hi => absurd hi (by omega),
      by simp [Costs], by simp⟩) fun st₀ hst k hk st hinv => ?_) (fun _ h => h)
      fun _ _ _ h => ⟨h.1, h.2⟩)
  · exact ⟨rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨hm, hrd, hcost, hpos⟩ := hinv
  refine (wp_seq).mpr ((wp_instr _).mpr ?_)
  simp only [Instr.run, Mode.sat_map]
  refine Mode.sat_write (hst.mono fun hW i hi => ?_) fun s' hs' => (wp_skip).mpr ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨len, hl, hlt⟩ := hW k hk
    exact ⟨len, by rw [hm.1]; exact hl, by rw [hidx]; omega⟩
  · refine (hm.trans (Modifies.of_write hs')).of_cells fun b i hb x hx => ?_
    have := blockDisjoint_iff.mp (hb _ List.mem_cons_self)
    rw [hidx] at hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rw [blockDisjoint_iff] <;> dsimp only at this ⊢ <;> omega
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Store.read_of_write_eq_some_of_ne hs' (Or.inr (by rw [hidx]; omega))]
      exact hrd i hi
    · rw [hidx] at hs'
      rw [Store.read_of_write_eq_some hs', hpos, Function.update_self]
  · change st.cnt + I.charge (.draw p d) = st₀.cnt + (k + 1) • I.charge (.draw p d)
    rw [hcost, succ_nsmul, add_assoc]
  · change Function.update st.pos d (st.pos d + 1) = _
    rw [hpos, Function.update_self, Function.update_idem, Nat.add_assoc]

end Instructions

/-! ### Certificates as specifications -/

section Certificates

variable {I : Interp P ι K C}

/-- **A footprint certificate is a specification**: from a state satisfying `pre` with writable
outputs, the routine succeeds and modifies only its output blocks. -/
theorem IsBlockRoutine.routineSpec {tag : P} {pre : Store P K → Prop}
    {outs : List (ℕ × ℕ × ℕ)} {r : Builder P ι ℕ ℕ Unit} (h : IsBlockRoutine I tag pre outs r) :
    RoutineSpec .total I (fun st => pre st.store ∧ WritableBlocks st.store tag outs) r outs
      fun _ _ => True := by
  refine ⟨h.composable, fun st hst => ?_⟩
  obtain ⟨out, ys, hr, hw⟩ := h.run st hst.1 hst.2
  exact ⟨out, hr, Modifies.of_writeBlocks hw, trivial⟩

/-- **A certified matrix-vector routine is a specification**, for each decoded input $x$: it
modifies only the destination block, which then decodes to $y$ with
$\lVert \mathbf{A}x - y \rVert_2 \le c \lVert x \rVert_2$. -/
theorem IsMatvecRoutine.routineSpec {dec : P → K → ℝ} {tag : P} {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {c : ℝ} {pre : Store P K → Prop} {src dst : ℕ}
    {sOff dOff : IExp ℕ} {r : Builder P ι ℕ ℕ Unit}
    (h : IsMatvecRoutine I dec tag A c pre src dst sOff dOff r) (x : Fin N → ℝ) :
    RoutineSpec .total I (fun st => pre st.store ∧ ReadsDecoded st.store dec tag src sOff.eval x ∧
        Writable st.store tag dst dOff.eval N) r [(dst, dOff.eval, N)] fun _ st' =>
      ∃ y : Fin N → ℝ, ReadsDecoded st'.store dec tag dst dOff.eval y ∧
        ‖WithLp.toLp 2 (Matrix.mulVec A x - y)‖ ≤ c * ‖WithLp.toLp 2 x‖ := by
  refine ⟨h.composable, fun st hst => ?_⟩
  obtain ⟨out, W, hr, hw, he⟩ := h.run st x hst.1 hst.2.1 hst.2.2
  have hm := Modifies.of_writeBlock hw
  rw [Array.size_ofFn] at hm
  refine ⟨out, hr, hm, fun i => dec tag (W i), fun i => ⟨W i, ?_, rfl⟩, he⟩
  rw [Store.read_of_writeBlock_eq_some_of_lt hw (by rw [Array.size_ofFn]; exact i.2)]
  simp

end Certificates

/-! ### Budgets -/

/-- **A total triple of a compiled program runs within its static budget**: success from the
triple, the counts and the workspace from the fixed first-order tree
(`NLAlib.Computation.Prog.runsWithin_staticCost_of_exec_eq_some`). -/
theorem Triple.prog_runsWithin {I : Interp P ι K (OpCount P ι)} {r b : ℕ} (prog : Prog P ι r b)
    (N : ℕ) (n : Fin r → ℕ) {pre : St P K (OpCount P ι) → Prop}
    {post : St P K (OpCount P ι) → St P K (OpCount P ι) → Prop}
    (h : Triple .total I pre (prog.toStmt N n) post) {st : St P K (OpCount P ι)} (hpre : pre st)
    (hsize : st.store.size = b) :
    prog.RunsWithin I N n st (prog.staticCost I.charge I.width N n).count
      (fun p => max (st.peak p) (st.cur p +
        (prog.staticCost I.charge I.width N n).cells p) + I.romSize p) (post st) := by
  obtain ⟨st', hrun, hp⟩ := h.exists_exec hpre
  rw [← Prog.exec_eq_exec_toStmt] at hrun
  obtain ⟨hs, _, h₁, h₂, h₃, rfl⟩ :=
    Prog.runsWithin_staticCost_of_exec_eq_some I prog N n hsize hrun
  exact ⟨hs, _, h₁, h₂, h₃, hp⟩

/-! ### Tactics -/

/-- Footprint side goals: membership in, disjointness of, distinctness of and arithmetic on
concrete block lists. `fp_omega [h₁, …]` adds the facts `hᵢ` (layout bounds such as
`Nat.mul_le_mul hr hk`), unfolds `NLAlib.Computation.BlocksDisjoint`,
`NLAlib.Computation.matBlock`, `List.Nodup` and `NLAlib.Computation.blockDisjoint_iff` in the
goal and those facts only (never the whole context), normalises products with `ring_nf` (so
`r * k` and `k * r` are one atom), and closes with `omega`. Only the goal and the passed facts
are normalised (`n * n` becomes `n ^ 2` there), so a context hypothesis with a product is a
different atom: **every hypothesis with a product that the goal needs must be passed**
(`fp_omega [Nat.mul_le_mul hr hk, hlen]`, not `fp_omega [Nat.mul_le_mul hr hk]` with `hlen` in
the context). -/
syntax "fp_omega" (" [" term,* "]")? : tactic

/-- The closing step of `fp_omega` on the goal and the named facts. -/
syntax "fp_close" (ppSpace colGt ident)* : tactic

macro_rules
  | `(tactic| fp_close $names*) => `(tactic| (
      (try simp only [BlocksDisjoint, matBlock, List.nodup_cons, List.nodup_nil, List.mem_cons,
        List.mem_append, List.not_mem_nil, or_false, and_true, not_or, forall_eq_or_imp,
        forall_eq, List.forall_mem_cons, blockDisjoint_iff, ne_eq, not_false_eq_true] at $names* ⊢)
      (try ring_nf at $names* ⊢)
      omega))

macro_rules
  | `(tactic| fp_omega) => `(tactic| fp_close)
  | `(tactic| fp_omega [$hs,*]) => do
      let mut names : Array (Lean.TSyntax `ident) := #[]
      for _ in hs.getElems do
        names := names.push (Lean.mkIdent (Lean.Name.mkSimple s!"fp_fact{names.size}"))
      let mut tac ← `(tactic| fp_close $names*)
      for (h, nm) in (hs.getElems.zip names).reverse do
        tac ← `(tactic| (have $nm := $h; $tac:tactic))
      return tac

/-- One step of a program proof: split a sequence, apply the triple `h` to its first statement
and leave its precondition and the continuation from the named next state; footprint side
goals closed by `assumption` or `fp_omega` are removed, the others stay in order (precondition,
continuation). -/
syntax "spec_step " term : tactic

macro_rules
  | `(tactic| spec_step $h) => `(tactic| (
      first | rw [wp_seq] | skip
      (refine Triple.wp_of $h ?_ ?_) <;> try (first | assumption | fp_omega)))

/-- One call of a specified routine in a builder: `NLAlib.Computation.RoutineSpec.wp_bind`, with
side goals closed by `assumption` or `fp_omega` removed, as for `spec_step`. -/
syntax "spec_call " term : tactic

macro_rules
  | `(tactic| spec_call $h) => `(tactic| (
      first
        | (refine RoutineSpec.wp_bind $h ?_ ?_) <;> try (first | assumption | fp_omega)
        | (refine RoutineSpec.wp_run $h ?_ ?_) <;> try (first | assumption | fp_omega)))

end NLAlib.Computation
