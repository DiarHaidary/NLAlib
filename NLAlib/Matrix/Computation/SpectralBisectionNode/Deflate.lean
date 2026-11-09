/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Matrix.Computation.SpectralBisectionTape
public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Computation.KernelCall
public import NLAlib.Computation.BLASCongr
public import NLAlib.Matrix.Computation.PairKernels.Arithmetic

/-!
# The leaf, child and deflation blocks of the spectral bisection node step

The blocks of the node step of `NLAlib.eighProg` that end a node or deflate it compute the matching
operations of `NLAlib.eighStep` on the machine of the semantics: a leaf writes the identity basis
and the diagonal, a node with one child writes the shifted matrix on the same slot, and the
deflation block writes the basis that `NLAlib.deflate` computes from the stored samples. Each value
statement is a partial equality: under kernels that are routines on pairs and a semantics that
decides flags, a successful run writes exactly the machine's value.

## Main results

* `NLAlib.holds_of_exec_eighLeafBlock`, `NLAlib.holds_of_exec_eighChildBlock`: the leaf and the
  child.
* `NLAlib.spec_eighChildBlock`: the child as a routine specification of the program logic.
* `NLAlib.spec_eighDeflateBlock_frame`, `NLAlib.spec_eighDeflateBlock`: the deflation as a routine
  specification of the program logic.
* `NLAlib.pairLayout_holds_unique`: a block holds at most one matrix.
* `NLAlib.holds_of_exec_eighDeflateBlock`, `NLAlib.exists_exec_eighDeflateBlock`: the deflation
  block computes, and succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The blocks of a node -/

/-- **A leaf as a routine specification**, in every mode: from a state holding the
$k \times k$ matrix $\mathbf{A}$ at `mo` of `Ma`, the run of `NLAlib.eighLeafBlock` modifies only
the identity block at `uo` of `Ua`, the $k$ cells from `eo` of `Ea` and the kind cell, which then
hold the machine's identity, the real diagonal of $\mathbf{A}$ (`diag`) or the machine's zero, and
the literal $1$; it keeps the tape positions; in mode `total` it also succeeds, given the literals
$0$ and $1$ and the three output blocks writable. No printed source. -/
theorem spec_eighLeafBlock (md : Mode) (p : P) (diag : Bool) (k : ℕ) {Ma Ua Ea : ℕ}
    {mo uo eo : IExp ℕ} {kd : Cell ℕ ℕ} (A : Matrix (Fin k) (Fin k) (K × K))
    (hUA : blockDisjoint (Ua, uo.eval, 2 * (k * k)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hEA : blockDisjoint (Ea, eo.eval, k) (Ma, mo.eval, 2 * (k * k)) = true)
    (hUE : blockDisjoint (Ua, uo.eval, 2 * (k * k)) (Ea, eo.eval, k) = true)
    (hkd : ∀ x ∈ [(Ma, mo.eval, 2 * (k * k)), (Ua, uo.eval, 2 * (k * k)), (Ea, eo.eval, k)],
      blockDisjoint (kd.buf, kd.idx.eval, 1) x = true) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    RoutineSpec md I (fun st => pairLayout.Holds st.store p Ma mo.eval A ∧ md.Needs
        ((∃ v, I.sem.lit p 0 = some v) ∧ (∃ v, I.sem.lit p 1 = some v) ∧ WritableBlocks st.store p
          [(Ua, uo.eval, 2 * (k * k)), (Ea, eo.eval, k), (kd.buf, kd.idx.eval, 1)]))
      (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd)
      [(Ua, uo.eval, 2 * (k * k)), (Ea, eo.eval, k), (kd.buf, kd.idx.eval, 1)]
      fun st st' => pairLayout.Holds st'.store p Ua uo.eval (M.identityMat k) ∧
        (∀ i : Fin k, st'.store.read p Ea (eo.eval + i) =
          some (if diag then (A i i).1 else M.zero)) ∧
        st'.store.read p kd.buf kd.idx.eval = I.sem.lit p ((1 : ℕ) : ℚ) ∧ PosKept st st' := by
  intro M
  have hk2 : ∀ i < k, 2 * (i + k * i) + 1 < 2 * (k * k) := fun i hi => by nlinarith
  refine ⟨by exec_composable, fun st ⟨hA, hN⟩ => ?_⟩
  have hW := fun s (hs : Store.shape s = st.store.shape) b o l (hx : (b, o, l) ∈
      [(Ua, uo.eval, 2 * (k * k)), (Ea, eo.eval, k), (kd.buf, kd.idx.eval, 1)]) =>
    hN.mono fun h => (h.2.2 _ hx).of_shape_eq hs
  refine (spec_zidentity (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
    (normal := normal) md p k (Y := Ua) (yo := uo)).wp_bind ((Mode.needs_and.mpr ⟨hN,
      hW _ rfl Ua uo.eval (2 * (k * k)) (by simp)⟩).mono fun ⟨h, hw⟩ =>
        ⟨h.1, h.2.1, hw⟩)
    fun st₁ hm₁ ⟨hU, hp₁⟩ => ?_
  have hA₁ := (readsOnly_entryLayoutHolds _ p Ma _ A).of_modifies hA hm₁
    (show BlocksDisjoint [matBlock Ma mo.eval k k 2] _ by fp_omega [hUA])
  have tail : ∀ st₂, Modifies [(Ea, eo.eval, k)] st₁.store st₂.store → st₂.pos = st₁.pos →
      (∀ i : Fin k, st₂.store.read p Ea (eo.eval + i) = some (if diag then (A i i).1 else M.zero)) →
      Wp md I (Builder.ins (.litIdx p kd 1)).run (fun st' => Modifies
        [(Ua, uo.eval, 2 * (k * k)), (Ea, eo.eval, k), (kd.buf, kd.idx.eval, 1)] st.store
          st'.store ∧
        pairLayout.Holds st'.store p Ua uo.eval (M.identityMat k) ∧
        (∀ i : Fin k, st'.store.read p Ea (eo.eval + i) =
          some (if diag then (A i i).1 else M.zero)) ∧
        st'.store.read p kd.buf kd.idx.eval = I.sem.lit p ((1 : ℕ) : ℚ) ∧ PosKept st st') st₂ :=
    fun st₂ hm₂ hp₂ hE => (RoutineSpec.ins spec_litIdx_read).wp_run
      ((Mode.needs_and.mpr ⟨hN, hW _ (hm₂.1.trans hm₁.1) kd.buf kd.idx.eval 1 (by simp)⟩).mono
        fun ⟨h, hw⟩ =>
        ⟨by simpa using h.2.1, hw⟩) fun st₃ hm₃ ⟨hK, hp₃⟩ =>
      ⟨(hm₁.trans hm₂ |>.trans hm₃).mono (by simp),
        (readsOnly_entryLayoutHolds _ p Ua _ _).of_modifies hU (hm₂.trans hm₃)
          (show BlocksDisjoint [matBlock Ua uo.eval k k 2] _ by
            fp_omega [hUE, hkd (Ua, uo.eval, 2 * (k * k)) (by simp)]),
        fun i => ((readsOnly_read _ _ _ _).of_modifies (hE i) hm₃
          (by fp_omega [hkd (Ea, eo.eval, k) (by simp), i.2])).trans rfl, by simpa using hK,
        hp₃.trans (hp₂.trans hp₁)⟩
  cases diag
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have h1 := spec_forRange_lit (m := md) (I := I) (p := p) (q := 0) (n := .const k) (Y := Ea)
      (off := eo.eval) (didx := fun i => eo + .var i) fun i => rfl
    refine h1.wp_bind (st := st₁) (f := fun _ => Builder.ins (.litIdx p kd 1))
      ((Mode.needs_and.mpr ⟨hN, hW _ hm₁.1 Ea eo.eval k (by simp)⟩).mono fun h => ⟨h.1.1, h.2⟩)
      fun st₂ hm₂ hh => tail st₂ hm₂ hh.2 fun i => ?_
    obtain ⟨v, hv, hr⟩ := hh.1 i i.2
    rw [hr]
    simp [M, ScalarSem.toFloatMachine, hv]
  · simp only [↓reduceIte]
    have h1 := spec_forRange_copy (m := md) (I := I) (p := p) (n := .const k) (Y := Ea)
      (off := eo.eval) (X := Ma) (didx := fun i => eo + .var i)
      (sidx := fun i => mo + zidx (.const k) (.var i) (.var i))
      (fun i => if h : i < k then (A ⟨i, h⟩ ⟨i, h⟩).1 else default) (fun i => rfl) fun i hi => by
        have := hk2 i hi
        simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat, IExp.eval_const,
          IExp.eval_var]
        fp_omega [hEA, this]
    refine h1.wp_bind (st := st₁) (f := fun _ => Builder.ins (.litIdx p kd 1))
      ⟨fun i hi => ?_, hW _ hm₁.1 Ea eo.eval k (by simp)⟩
      fun st₂ hm₂ hh => tail st₂ hm₂ hh.2 fun i => by simpa using hh.1 i i.2
    have := hA₁ ⟨i, hi⟩ ⟨i, hi⟩ ⟨0, two_pos⟩
    simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat, IExp.eval_const,
      IExp.eval_var]
    rw [dif_pos (show i < k from hi)]
    simpa [pairLayout] using this

/-- A leaf writes its output: a successful run of `NLAlib.eighLeafBlock` for a node of size
$k$ whose matrix $\mathbf{A}$ is held at `mo` of `Ma` ends with the block at `uo` of `Ua` holding
the machine's identity (`NLAlib.FloatMachine.identityMat`), the cells $eo + i$ of `Ea` the real
parts $\operatorname{Re} a_{ii}$ (`diag`) or the machine's zero, and the kind cell the literal
$1$; every cell outside these blocks and the kind cell is unchanged, the store shape and the tape
positions too. No printed source. -/
theorem holds_of_exec_eighLeafBlock (p : P) (diag : Bool) (k : ℕ) {Ma Ua Ea : ℕ}
    {mo uo eo : IExp ℕ} {kd : Cell ℕ ℕ} {st st' : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (hUA : blockDisjoint (Ua, uo.eval, 2 * (k * k)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hEA : blockDisjoint (Ea, eo.eval, k) (Ma, mo.eval, 2 * (k * k)) = true)
    (hUE : blockDisjoint (Ua, uo.eval, 2 * (k * k)) (Ea, eo.eval, k) = true)
    (hkd : ∀ x ∈ [(Ma, mo.eval, 2 * (k * k)), (Ua, uo.eval, 2 * (k * k)), (Ea, eo.eval, k)],
      blockDisjoint (kd.buf, kd.idx.eval, 1) x = true)
    (h : exec I (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd).run st =
      some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Ua uo.eval (M.identityMat k) ∧
      (∀ i : Fin k, st'.store.read p Ea (eo.eval + i) = some (if diag then (A i i).1 else M.zero)) ∧
      st'.store.read p kd.buf kd.idx.eval = I.sem.lit p ((1 : ℕ) : ℚ) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Ua, uo.eval, 2 * (k * k)) = true →
        blockDisjoint (b, i, 1) (Ea, eo.eval, k) = true →
        blockDisjoint (b, i, 1) (kd.buf, kd.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M
  obtain ⟨hm, hU, hE, hK, hp⟩ := (spec_eighLeafBlock (toNat := toNat) (mmR := mmR) (qrR := qrR)
    (unif := unif) (normal := normal) .liberal p diag k A hUA hEA hUE hkd).spec.holds_of_exec
    ⟨hA, trivial⟩ h
  exact ⟨hU, hE, hK, fun q b i h1 h2 h3 => hm.2 q b i (by simp [h1, h2, h3]), hm.1, hp⟩

/-- **One child as a routine specification**: from a state holding the $k \times k$ matrix
$\mathbf{A}$ at `mo` of `Ma` and $\sigma$ in the cell `sg`, the run of `NLAlib.eighChildBlock`
modifies only the block at `mo'` of `Ma` (disjoint from the one at `mo`), the size cell and the
kind cell, writes the literals $k$ and `code` into the last two and keeps the tape positions; if
`sg` lies outside the output block, that block holds `M.hermShift A σ`. In mode `total` the run
also succeeds, given the standard model on every value and the three outputs writable. No printed
source. -/
theorem spec_eighChildBlock (md : Mode) {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ ∀ p x, safe p x)) (p : P) (k : ℕ)
    {Ma : ℕ} {mo mo' : IExp ℕ} {sg sz kd : Cell ℕ ℕ} (code : ℕ) (σ : K)
    (A : Matrix (Fin k) (Fin k) (K × K))
    (hAA : blockDisjoint (matBlock Ma mo'.eval k k 2) (matBlock Ma mo.eval k k 2) = true)
    (hsz : blockDisjoint (sz.buf, sz.idx.eval, 1) (matBlock Ma mo'.eval k k 2) = true)
    (hkd : blockDisjoint (kd.buf, kd.idx.eval, 1) (matBlock Ma mo'.eval k k 2) = true)
    (hszkd : blockDisjoint (sz.buf, sz.idx.eval, 1) (kd.buf, kd.idx.eval, 1) = true) :
    RoutineSpec md I (fun st => pairLayout.Holds st.store p Ma mo.eval A ∧
        st.store.read p sg.buf sg.idx.eval = some σ ∧
        md.Needs (Writable st.store p Ma mo'.eval (k * k * 2) ∧
          Writable st.store p sz.buf sz.idx.eval 1 ∧ Writable st.store p kd.buf kd.idx.eval 1))
      (eighChildBlock (ι := ι) p (.const k) Ma mo mo' sg sz kd code)
      [matBlock Ma mo'.eval k k 2, (sz.buf, sz.idx.eval, 1), (kd.buf, kd.idx.eval, 1)]
      fun st st' => (blockDisjoint (sg.buf, sg.idx.eval, 1) (matBlock Ma mo'.eval k k 2) = true →
          pairLayout.Holds st'.store p Ma mo'.eval
            ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift A σ)) ∧
        st'.store.read p sz.buf sz.idx.eval = I.sem.lit p ((k : ℕ) : ℚ) ∧
        st'.store.read p kd.buf kd.idx.eval = I.sem.lit p ((code : ℕ) : ℚ) ∧ PosKept st st' := by
  refine ⟨(executionComposable_named _ _ _).bind ((executionComposable_ins _).bind
    (executionComposable_ins _)), fun st ⟨hA, hσ, hN⟩ => ?_⟩
  have hL : ∀ q : ℚ, md.Needs (∃ v, I.sem.lit p q = some v) := fun q =>
    hsem.mono fun ⟨h, hs⟩ => h.lit_ok p q (hs _ _)
  have hW := fun s (hs : Store.shape s = st.store.shape) => hN.mono fun h =>
    (⟨h.1.of_shape_eq hs, h.2.1.of_shape_eq hs, h.2.2.of_shape_eq hs⟩ : Writable s p Ma mo'.eval
      (k * k * 2) ∧ Writable s p sz.buf sz.idx.eval 1 ∧ Writable s p kd.buf kd.idx.eval 1)
  exact (spec_zhermShift (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
    (normal := normal) md (hsem.mono fun ⟨h, hs⟩ => h.mono_safe fun p x _ => hs p x) p k
    (X := Ma) (Y := Ma) (xo := mo) (yo := mo') (c := sg) σ A hAA).wp_bind
    ⟨hA, hσ, (hW _ rfl).mono (·.1)⟩ fun st₁ hm₁ h₁ =>
    (RoutineSpec.ins (spec_litIdx_read (dst := sz) (e := .const k))).wp_bind
    (Mode.needs_and.mpr ⟨hL _, (hW _ hm₁.1).mono (·.2.1)⟩) fun st₂ hm₂ h₂ =>
    (RoutineSpec.ins (spec_litIdx_read (dst := kd) (e := .const code))).wp_run
    (Mode.needs_and.mpr ⟨hL _, (hW _ (hm₁.trans hm₂).1).mono (·.2.2)⟩) fun st₃ hm₃ h₃ =>
    ⟨(hm₁.trans hm₂ |>.trans hm₃).mono (by simp), fun hg =>
      (show ReadsOnly _ [matBlock Ma mo'.eval k k 2] from readsOnly_entryLayoutHolds pairLayout p
        Ma _ ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift A σ)).of_modifies
        (h₁.1 hg) (hm₂.trans hm₃) (by fp_omega [hsz, hkd]), by
      rw [(readsOnly_read _ _ _ _).of_modifies h₂.1 hm₃ (by fp_omega [hszkd])]; simp, by
      rw [h₃.1]; simp, h₃.2.trans (h₂.2.trans h₁.2)⟩

/-- One child on the same slot: a successful run of `NLAlib.eighChildBlock` for a node of size
$k$ whose matrix $\mathbf{A}$ is held at `mo` of `Ma`, the cell `sg` holding $\sigma$, ends with the
block at `mo'` of `Ma` (disjoint from the one at `mo`) holding `M.hermShift A σ`, the size cell the
literal $k$ and the kind cell the literal `code`; every other cell is unchanged, the store shape and
the tape positions too. No printed source. -/
theorem holds_of_exec_eighChildBlock (p : P) (k : ℕ) {Ma : ℕ} {mo mo' : IExp ℕ}
    {sg sz kd : Cell ℕ ℕ} (code : ℕ) {σ : K} {st st' : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hAA : blockDisjoint (Ma, mo'.eval, 2 * (k * k)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hsg : blockDisjoint (sg.buf, sg.idx.eval, 1) (Ma, mo'.eval, 2 * (k * k)) = true)
    (hsz : blockDisjoint (sz.buf, sz.idx.eval, 1) (Ma, mo'.eval, 2 * (k * k)) = true)
    (hkd : blockDisjoint (kd.buf, kd.idx.eval, 1) (Ma, mo'.eval, 2 * (k * k)) = true)
    (hszkd : blockDisjoint (sz.buf, sz.idx.eval, 1) (kd.buf, kd.idx.eval, 1) = true)
    (h : exec I (eighChildBlock (ι := ι) p (.const k) Ma mo mo' sg sz kd code).run st =
      some st') :
    pairLayout.Holds st'.store p Ma mo'.eval
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift A σ) ∧
      st'.store.read p sz.buf sz.idx.eval = I.sem.lit p ((k : ℕ) : ℚ) ∧
      st'.store.read p kd.buf kd.idx.eval = I.sem.lit p ((code : ℕ) : ℚ) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Ma, mo'.eval, 2 * (k * k)) = true →
        blockDisjoint (b, i, 1) (sz.buf, sz.idx.eval, 1) = true →
        blockDisjoint (b, i, 1) (kd.buf, kd.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have e : ∀ a b : ℕ, a * b * 2 = 2 * (a * b) := fun a b => by ring
  obtain ⟨hm, hv, hsz', hkd', hp⟩ := (spec_eighChildBlock (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) (u := fun _ => 0) (dec := fun _ _ => 0)
    (safe := fun _ _ => True) .liberal trivial p k code σ A (by simpa [matBlock, e] using hAA)
    (by simpa [matBlock, e] using hsz) (by simpa [matBlock, e] using hkd) hszkd).spec.holds_of_exec
    ⟨hA, hσ, trivial⟩ h
  exact ⟨hv (by simpa [matBlock, e] using hsg), hsz', hkd', fun q b i h₁ h₂ h₃ => hm.2 q b i
    (by fp_omega [h₁, h₂, h₃]), hm.1, hp⟩

/-- One entry of the test-matrix loop of a deflation: the two products of the words of `Sg` by the
stored $\sqrt{1/2}$ land in the words $2(i + kj)$ and $2(i + kj) + 1$ of `G`; the earlier entries,
every other buffer, the shape and the positions are kept. -/
private theorem deflate_testEntry (p : P) (n k lo s i j : ℕ) {Sg G : ℕ} {sq : Cell ℕ ℕ}
    {sv : K} {st s₁ s₂ : St P K C} (hi : i < k) (hsqG : sq.buf ≠ G) (hSgG : Sg ≠ G)
    (hsq : st.store.read p sq.buf sq.idx.eval = some sv)
    (hsh : s₁.store.shape = st.store.shape) (hps : s₁.pos = st.pos)
    (hfr : ∀ q b x, b ≠ G → s₁.store.read q b x = st.store.read q b x)
    (hent : ∀ i' j', i' < k → j' < k → i' + k * j' < i + k * j → ∃ a a',
      st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i')) = some a ∧
      st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i') + 1) = some a' ∧
      s₁.store.read p G (2 * (i' + k * j')) = some ((I.sem.bin p .mul a sv).getD default) ∧
      s₁.store.read p G (2 * (i' + k * j') + 1) = some ((I.sem.bin p .mul a' sv).getD default))
    (hex : exec I (.seq (.instr (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j)⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i)⟩ sq))
        (.seq (.instr (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j) + 1⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i) + 1⟩ sq))
        .skip)) s₁ = some s₂) :
    s₂.store.shape = st.store.shape ∧ s₂.pos = st.pos ∧
      (∀ q b x, b ≠ G → s₂.store.read q b x = st.store.read q b x) ∧
      ∀ i' j', i' < k → j' < k → i' + k * j' < i + k * j + 1 → ∃ a a',
        st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i')) = some a ∧
        st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i') + 1) = some a' ∧
        s₂.store.read p G (2 * (i' + k * j')) = some ((I.sem.bin p .mul a sv).getD default) ∧
        s₂.store.read p G (2 * (i' + k * j') + 1) =
          some ((I.sem.bin p .mul a' sv).getD default) := by
  rw [exec_seq, exec_instr] at hex
  obtain ⟨s₃, h₃, hex⟩ := Option.bind_eq_some_iff.mp hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₃ hex
  obtain ⟨_, ⟨a, ha, c, hc, v, hv, w₁, hw₁, rfl⟩, rfl⟩ := h₃
  obtain ⟨_, ⟨a', ha', c', hc', v', hv', w₂, hw₂, rfl⟩, rfl⟩ := hex
  simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
    IExp.eval_ofNat] at ha hc hv hw₁ ha' hc' hv' hw₂
  have hsq₁ : s₁.store.read p sq.buf sq.idx.eval = some sv := (hfr _ _ _ hsqG).trans hsq
  rw [hsq₁, Option.some.injEq] at hc
  subst hc
  rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hsqG), hsq₁, Option.some.injEq] at hc'
  subst hc'
  rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hSgG)] at ha'
  have hfr₂ : ∀ q b x, b ≠ G → w₂.read q b x = st.store.read q b x := fun q b x hb => by
    rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hb), hfr q b x hb]
  refine ⟨(Store.shape_of_write_eq_some hw₂).trans ((Store.shape_of_write_eq_some hw₁).trans hsh),
    hps, hfr₂, fun i' j' hi' hj' hlt => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | he
  · obtain ⟨b₁, b₂, hb₁, hb₂, hg₁, hg₂⟩ := hent i' j' hi' hj' hlt
    refine ⟨b₁, b₂, hb₁, hb₂, ?_, ?_⟩
    · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega)), hg₁]
    · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega)), hg₂]
  · obtain ⟨rfl, rfl⟩ : i' = i ∧ j' = j := by
      have hk : 0 < k := by omega
      have h1 : (i' + k * j') % k = (i + k * j) % k := by rw [he]
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h1
      subst h1
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hk (by omega)⟩
    refine ⟨a, a', (hfr _ _ _ hSgG).symm.trans ha, (hfr _ _ _ hSgG).symm.trans ha', ?_, ?_⟩
    · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega)),
        Store.read_of_write_eq_some hw₁, hv]
      rfl
    · rw [Store.read_of_write_eq_some hw₂, hv']
      rfl

/-- The test-matrix loop of a deflation: entry $(i, j)$ of the block `G` is the pair of products of
the words $2(n(2(lo + j) + s) + i)$ and the next of `Sg` by the stored $\sqrt{1/2}$; every other
buffer, the shape and the positions are kept. -/
private theorem deflate_testLoop (p : P) (n k lo s : ℕ) {Sg G : ℕ} {sq : Cell ℕ ℕ}
    {sv : K} {st st' : St P K C} (hsqG : sq.buf ≠ G) (hSgG : Sg ≠ G)
    (hsq : st.store.read p sq.buf sq.idx.eval = some sv)
    (h : exec I (.loop (.const k) fun j => (forRange (ι := ι) (.const k) fun i => do
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j)⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i)⟩ sq)
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j) + 1⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i) + 1⟩ sq)).run)
      st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ q b x, b ≠ G → st'.store.read q b x = st.store.read q b x) ∧
      ∀ i j, i < k → j < k → ∃ a a',
        st.store.read p Sg (2 * (n * (2 * (lo + j) + s) + i)) = some a ∧
        st.store.read p Sg (2 * (n * (2 * (lo + j) + s) + i) + 1) = some a' ∧
        st'.store.read p G (2 * (i + k * j)) = some ((I.sem.bin p .mul a sv).getD default) ∧
        st'.store.read p G (2 * (i + k * j) + 1) =
          some ((I.sem.bin p .mul a' sv).getD default) := by
  let Ent : ℕ → St P K C → Prop := fun c s₁ => ∀ i' j', i' < k → j' < k → i' + k * j' < c →
    ∃ a a', st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i')) = some a ∧
      st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i') + 1) = some a' ∧
      s₁.store.read p G (2 * (i' + k * j')) = some ((I.sem.bin p .mul a sv).getD default) ∧
      s₁.store.read p G (2 * (i' + k * j') + 1) = some ((I.sem.bin p .mul a' sv).getD default)
  have hR := forall_of_exec_loop_eq_some I (n := .const k) (fun j s₁ => s₁.store.shape =
      st.store.shape ∧ s₁.pos = st.pos ∧
      (∀ q b x, b ≠ G → s₁.store.read q b x = st.store.read q b x) ∧ Ent (k * j) s₁)
    ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ h => absurd h (by omega)⟩ ?_ h
  · obtain ⟨hsh, hps, hfr, hent⟩ := hR
    exact ⟨hsh, hps, hfr, fun i j hi hj => hent i j hi hj (by
      simp only [IExp.eval_const]; nlinarith)⟩
  rintro j hj s₁ s₂ ⟨hsh, hps, hfr, hent⟩ hex
  change exec I (.seq (.loop _ _) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip] at hex
  have hR' := forall_of_exec_loop_eq_some I (n := .const k) (fun i s₃ => s₃.store.shape =
      st.store.shape ∧ s₃.pos = st.pos ∧
      (∀ q b x, b ≠ G → s₃.store.read q b x = st.store.read q b x) ∧ Ent (i + k * j) s₃)
    ⟨hsh, hps, hfr, by rwa [zero_add]⟩ (fun i hi s₃ s₄ ⟨hsh, hps, hfr, hent⟩ hex => by
      rw [show i + 1 + k * j = i + k * j + 1 by ring]
      exact deflate_testEntry p n k lo s i j hi hsqG hSgG hsq hsh hps hfr hent hex) hex
  obtain ⟨hsh, hps, hfr, hent⟩ := hR'
  refine ⟨hsh, hps, hfr, ?_⟩
  simp only [IExp.eval_const] at hent
  rwa [show k * (j + 1) = k + k * j by ring]

/-- Randomized deflation on stored samples computes `NLAlib.deflate`: if kernels `mm`, `qr` of
`I` are the routines `mmR`, `qrR` on interleaved pairs, a successful run of
`NLAlib.eighDeflateBlock` for a node of size $k \le n$ at slot $lo$ of depth $d$ with rank
$r \le k$, side $b$, the stored projector $\mathbf{P}$ ($k \times k$) at offset $0$ of `Pm`, the
cell `sq` holding the stored $\sqrt{1/2}$ (`NLAlib.Computation.ScalarSem.sqrtHalf`) and the $4n^2$
Gaussian words of the level in `Sg` (word $w$ the tape value at position $4n^2 d + w$), ends with
the block at `qo` of `Qa` holding `NLAlib.deflate M r P G` for $\mathbf{G}$ the leading $k \times k$
block of the test matrix of side $b$ of the node's samples (`NLAlib.eighTapeSample`), $M$ the
machine of the interpretation (`NLAlib.eighTapeMachine`); every cell outside that block and the
scratch buffers `G`, `Y`, `Qf`, `Rf` is unchanged, the store shape and the tape positions too. No
printed source. -/
theorem holds_of_exec_eighDeflateBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n k r d lo : ℕ) (hk : lo + k ≤ n)
    (hr : r ≤ k) (b : Bool) {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ} {qo : IExp ℕ}
    {st st' : St P K C} {Pmat : Matrix (Fin k) (Fin k) (K × K)}
    (hP : pairLayout.Holds st.store p Pm 0 Pmat)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (h : exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
      (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st') :
    pairLayout.Holds st'.store p Qa qo.eval
        (deflate (eighTapeMachine I p mmR qrR) r Pmat
          (leadingBlock k ((eighTapeSample n d lo).2 b))) ∧
      (∀ q b' i, b' ∉ [G, Y, Qf, Rf] → blockDisjoint (b', i, 1) (Qa, qo.eval, 2 * (k * r)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  set M := eighTapeMachine I p mmR qrR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hsqb
  obtain ⟨⟨-, hSgG, -, -, -, -⟩, ⟨hPmG, hPmY, -, -, -⟩, ⟨hGY, -, -, -⟩, ⟨hYQf, hYRf, -⟩,
    ⟨hQfRf, hQfQa⟩, -, -⟩ := hbufs
  obtain ⟨hsG, -, -, -, -⟩ := hsqb
  have hne : ∀ {b b' i i' l l' : ℕ}, b ≠ b' → blockDisjoint (b, i, l) (b', i', l') = true :=
    fun h => by simp [blockDisjoint, h]
  change exec I (.seq (.loop _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) .skip)))) st = some st' at h
  rw [exec_seq] at h
  obtain ⟨s₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₃, h₃, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c₂, hc₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
  obtain ⟨c₃, hc₃, rfl⟩ := Option.map_eq_some_iff.mp h₃
  -- the stored test matrix
  obtain ⟨hsh₁, hps₁, hfr₁, hent⟩ := deflate_testLoop p n k lo (if b then 0 else 1) hsG hSgG
    hsq h₁
  have hG : pairLayout.Holds s₁.store p G 0
      ((leadingBlock k ((eighTapeSample n d lo).2 b)).map M.normal) := by
    intro i j t
    obtain ⟨a, a', ha, ha', hg, hg'⟩ := hent i j i.isLt j.isLt
    have hw : 2 * (n * (2 * (lo + j) + (if b then 0 else 1)) + i) + 1 < 4 * (n * n) := by
      have h1 : 2 * (lo + j) + (if b then 0 else 1) + 1 ≤ 2 * n := by split <;> omega
      have h2 := Nat.mul_le_mul_left n h1
      have h3 : (i : ℕ) < n := by omega
      rw [Nat.mul_add, Nat.mul_one] at h2
      nlinarith
    rw [hSg _ (by omega)] at ha
    rw [hSg _ hw] at ha'
    cases ha
    cases ha'
    have hidx : 4 * (n * n) * d + 2 * (n * (2 * (lo + j) + (if b then 0 else 1)) + i) =
        2 * (2 * (n * n) * d + n * (2 * (lo + j) + (if b then 0 else 1)) + i) := by ring
    have hidx' : 4 * (n * n) * d + (2 * (n * (2 * (lo + j) + (if b then 0 else 1)) + i) + 1) =
        2 * (2 * (n * n) * d + (n * (2 * (lo + j) + (if b then 0 else 1)) + i)) + 1 := by ring
    have hi : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨by omega, by omega⟩
    obtain ⟨t, ht⟩ := t
    change t < 2 at ht
    change s₁.store.read p G (0 + (2 * ((i : ℕ) + k * j) + t)) = _
    interval_cases t
    · rw [zero_add, add_zero, hg]
      simp [pairLayout, leadingBlock, hi, eighTapeSample, M, eighTapeMachine,
        ScalarSem.toFloatMachine, ScalarSem.tapeNormal, hidx]
    · rw [zero_add, hg']
      simp [pairLayout, leadingBlock, hi, eighTapeSample, M, eighTapeMachine,
        ScalarSem.toFloatMachine, ScalarSem.tapeNormal, hidx', add_assoc]
  -- the two kernel calls
  obtain ⟨hY, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p (l := k) (m := k)
    (n := k) (a := (Pm, 0)) (b := (G, 0)) (c := (Y, 0))
    (hP.of_forall_read_eq fun i _ _ => hfr₁ p Pm i hPmG) hG (hne (Ne.symm hPmY))
    (hne (Ne.symm hGY)) hc₂
  obtain ⟨hQf, -, hfr₃⟩ := hqr.holds_of_kcallStore_eq_some (fun _ => rfl) p (m := k) (n := k)
    (a := (Y, 0)) (q := (Qf, 0)) (r := (Rf, 0)) hY (hne hQfRf) (hne (Ne.symm hYQf))
    (hne (Ne.symm hYRf)) hc₃
  -- the copy of the first `r` columns
  rw [exec_seq_skip] at h
  obtain ⟨hQa, hfr₄, hsh₄, hps₄⟩ := holds_of_exec_zcopy (I := I) p k r
    (A := Matrix.of fun i (j : Fin r) => (qrR (mmR Pmat
      ((leadingBlock k ((eighTapeSample n d lo).2 b)).map M.normal))).1 i
        ⟨j, lt_of_lt_of_le j.isLt hr⟩)
    (fun i j t => hQf i ⟨j, lt_of_lt_of_le j.isLt hr⟩ t) (hne (Ne.symm hQfQa))
    ((exec_seq_skip I _ _).trans h)
  refine ⟨?_, fun q b' i hb' hbd => ?_, ?_, ?_⟩
  · convert hQa using 1
    refine Matrix.ext fun i j => ?_
    simp only [deflate, dif_pos (lt_of_lt_of_le j.isLt hr), Matrix.of_apply]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb'
    rw [hfr₄ q b' i hbd, hfr₃ q b' i (hne hb'.2.2.1) (hne hb'.2.2.2), hfr₂ q b' i (hne hb'.2.1),
      hfr₁ q b' i hb'.1]
  · rw [hsh₄]
    change c₃.shape = _
    rw [Interp.shape_of_kcallStore_eq_some hc₃, Interp.shape_of_kcallStore_eq_some hc₂, hsh₁]
  · rw [hps₄]
    exact hps₁

omit [Inhabited K] in
/-- The test-matrix loop of a deflation succeeds when the words of `Sg` it reads and the cell `sq`
are initialised and `G` is long enough; it keeps the shape and every other buffer, and initialises
the first $2k^2$ words of `G`. -/
private theorem exists_exec_deflate_testLoop {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n k lo s : ℕ) {Sg G lenG : ℕ}
    {sq : Cell ℕ ℕ} {sv : K} {st : St P K C} (hsqG : sq.buf ≠ G) (hSgG : Sg ≠ G)
    (hsq : st.store.read p sq.buf sq.idx.eval = some sv)
    (hSg : ∀ i j, i < k → j < k → ∀ t < 2, ∃ a,
      st.store.read p Sg (2 * (n * (2 * (lo + j) + s) + i) + t) = some a)
    (hG : st.store.shape[G]? = some (p, lenG)) (hlen : 2 * (k * k) ≤ lenG) :
    ∃ st', exec I (.loop (.const k) fun j => (forRange (ι := ι) (.const k) fun i => do
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j)⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i)⟩ sq)
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j) + 1⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i) + 1⟩ sq)).run)
      st = some st' ∧ st'.store.shape = st.store.shape ∧
      (∀ q b x, b ≠ G → st'.store.read q b x = st.store.read q b x) ∧
      ∀ w < 2 * (k * k), ∃ v, st'.store.read p G w = some v := by
  let R : ℕ → St P K C → Prop := fun c s₁ => s₁.store.shape = st.store.shape ∧
    (∀ q b x, b ≠ G → s₁.store.read q b x = st.store.read q b x) ∧
    ∀ w < 2 * c, ∃ v, s₁.store.read p G w = some v
  have hkeep : ∀ {s s' : Store P K} {x : ℕ} {z : K}, s.write p G x z = some s' →
      ∀ w, (∃ v, s.read p G w = some v) → ∃ v, s'.read p G w = some v := by
    intro s s' x z hw w ⟨v, hv⟩
    by_cases hwx : w = x
    · subst hwx; exact ⟨z, Store.read_of_write_eq_some hw⟩
    · exact ⟨v, (Store.read_of_write_eq_some_of_ne hw (Or.inr hwx)).trans hv⟩
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := .const k) (fun j s₁ => R (k * j) s₁)
    ⟨rfl, fun _ _ _ _ => rfl, fun w hw => absurd hw (by simp)⟩ ?_).imp
    fun st' h => ⟨h.1, h.2⟩
  intro j hj s₁ ⟨hsh₁, hfr₁, hw₁⟩
  simp only [IExp.eval_const] at hj
  change ∃ st', exec I (.seq (.loop (.const k) _) .skip) s₁ = some st' ∧ _
  simp only [exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := .const k)
    (fun i s₂ => R (i + k * j) s₂) ⟨hsh₁, hfr₁, by simpa using hw₁⟩ ?_).imp
    fun st' h => ⟨h.1, by
      have := h.2
      rwa [IExp.eval_const, show k + k * j = k * (j + 1) by ring] at this⟩
  intro i hi s₂ ⟨hsh₂, hfr₂, hw₂⟩
  simp only [IExp.eval_const] at hi
  obtain ⟨a, ha⟩ := hSg i j hi hj 0 (by norm_num)
  obtain ⟨a', ha'⟩ := hSg i j hi hj 1 (by norm_num)
  obtain ⟨z, hz⟩ := hsem.bin_ok p .mul a sv trivial (fun h => nomatch h) trivial
  obtain ⟨z', hz'⟩ := hsem.bin_ok p .mul a' sv trivial (fun h => nomatch h) trivial
  have hidx : 2 * (i + k * j) + 1 < lenG := by nlinarith
  obtain ⟨w₁, hw₁'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := s₂.store) z
    (hsh₂ ▸ hG) (show 2 * (i + k * j) < lenG by omega)
  obtain ⟨w₂, hw₂'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := w₁) z'
    ((Store.shape_of_write_eq_some hw₁').trans hsh₂ ▸ hG) hidx
  have hsq₂ : s₂.store.read p sq.buf sq.idx.eval = some sv := (hfr₂ _ _ _ hsqG).trans hsq
  change ∃ st', exec I (.seq (.instr _) (.seq (.instr _) .skip)) s₂ = some st' ∧ R _ st'
  rw [exec_seq_instr_bin I (a := a) (c := sv) (by
        simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
          IExp.eval_ofNat]
        rw [hfr₂ _ _ _ hSgG]; simpa using ha) hsq₂ hz (by
        simpa [zidx] using hw₁'),
      exec_seq_instr_bin I (a := a') (c := sv) (by
        simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
          IExp.eval_ofNat]
        rw [Store.read_of_write_eq_some_of_ne hw₁' (Or.inl hSgG), hfr₂ _ _ _ hSgG]
        exact ha')
        ((Store.read_of_write_eq_some_of_ne hw₁' (Or.inl hsqG)).trans hsq₂) hz' (by
        simpa [zidx] using hw₂'), exec_skip]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · exact (Store.shape_of_write_eq_some hw₂').trans ((Store.shape_of_write_eq_some hw₁').trans hsh₂)
  · intro q b x hb
    rw [Store.read_of_write_eq_some_of_ne hw₂' (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw₁' (Or.inl hb), hfr₂ q b x hb]
  · intro w hw
    by_cases hw' : w < 2 * (i + k * j)
    · exact hkeep hw₂' w (hkeep hw₁' w (hw₂ w hw'))
    · by_cases he : w = 2 * (i + k * j) + 1
      · subst he; exact ⟨z', Store.read_of_write_eq_some hw₂'⟩
      · have he' : w = 2 * (i + k * j) := by omega
        subst he'
        exact hkeep hw₂' _ ⟨z, Store.read_of_write_eq_some hw₁'⟩

omit [Inhabited K] in
/-- The final copy of a deflation: from a store holding a $k \times k$ matrix at the block $0$ of
`Qf`, equal to the store of `st` outside the scratch buffers `G`, `Y`, `Qf`, `Rf` and of the
same shape, a block at `qo` of `Qa` (another buffer) with room for $2kr$ cells receives the first
$r \le k$ columns: the copy succeeds, the block holds some matrix, every other cell outside the
scratch buffers is that of `st` and the shape is kept. -/
private theorem exists_exec_zcopy_deflate (p : P) {k r : ℕ} (hr : r ≤ k) {G Y Qf Rf Qa : ℕ}
    {qo : IExp ℕ} {S st : St P K C} {Qk : Matrix (Fin k) (Fin k) (K × K)}
    (hQf : pairLayout.Holds S.store p Qf 0 Qk) (hQfQa : Qa ≠ Qf)
    (hQa : ∃ len, S.store.shape[Qa]? = some (p, len) ∧ qo.eval + 2 * (k * r) ≤ len)
    (hfr : ∀ q b' i, b' ∉ [G, Y, Qf, Rf] → S.store.read q b' i = st.store.read q b' i)
    (hsh : S.store.shape = st.store.shape) :
    ∃ st', exec I (zcopy (ι := ι) p (.const k) (.const r) Qf 0 Qa qo).run S = some st' ∧
      (∃ Q : Matrix (Fin k) (Fin r) (K × K), pairLayout.Holds st'.store p Qa qo.eval Q) ∧
      (∀ q b' i, b' ∉ [G, Y, Qf, Rf] →
        blockDisjoint (b', i, 1) (Qa, qo.eval, 2 * (k * r)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape := by
  have hne : blockDisjoint (Qa, qo.eval, 2 * (k * r)) (Qf, (0 : IExp ℕ).eval, 2 * (k * r)) =
      true := by simp [blockDisjoint, hQfQa]
  have hQm : pairLayout.Holds S.store p Qf (0 : IExp ℕ).eval
      (fun i (j : Fin r) => Qk i ⟨j, lt_of_lt_of_le j.isLt hr⟩) :=
    fun i j t => hQf i ⟨j, lt_of_lt_of_le j.isLt hr⟩ t
  obtain ⟨st', hst'⟩ := exists_exec_zcopy (I := I) p k r (st := S) (X := Qf) (xo := 0)
    (Y := Qa) (yo := qo) hQm hne hQa
  obtain ⟨hQa', hfrc, hshc, -⟩ := holds_of_exec_zcopy (I := I) p k r hQm hne hst'
  exact ⟨st', hst', ⟨_, hQa'⟩, fun q b' i hb' hbd => (hfrc q b' i hbd).trans (hfr q b' i hb'),
    hshc.trans hsh⟩

/-- Deflation on stored samples succeeds, with what it writes: some matrix at the block `qo`
of `Qa`, every other cell outside the scratch buffers unchanged, the shape kept. -/
theorem exists_exec_eighDeflateBlock_facts {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n k r _d lo : ℕ)
    (hk : lo + k ≤ n) (hr : r ≤ k) (b : Bool) {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ}
    {qo : IExp ℕ} {st : St P K C} {Pmat : Matrix (Fin k) (Fin k) (K × K)}
    (hP : pairLayout.Holds st.store p Pm 0 Pmat)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (hscr : ∀ X ∈ [G, Y, Qf, Rf], ∃ len, st.store.shape[X]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hQa : ∃ len, st.store.shape[Qa]? = some (p, len) ∧ qo.eval + 2 * (k * r) ≤ len) :
    ∃ st', exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
      (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st' ∧
      (∃ Q : Matrix (Fin k) (Fin r) (K × K), pairLayout.Holds st'.store p Qa qo.eval Q) ∧
      (∀ q b' i, b' ∉ [G, Y, Qf, Rf] → blockDisjoint (b', i, 1) (Qa, qo.eval, 2 * (k * r)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hsqb
  obtain ⟨⟨-, hSgG, -, -, -, -⟩, ⟨hPmG, hPmY, -, -, -⟩, ⟨hGY, -, -, -⟩, ⟨hYQf, hYRf, -⟩,
    ⟨hQfRf, hQfQa⟩, -, -⟩ := hbufs
  obtain ⟨hsG, -, -, -, -⟩ := hsqb
  have hne : ∀ {b b' i i' l l' : ℕ}, b ≠ b' → blockDisjoint (b, i, l) (b', i', l') = true :=
    fun h => by simp [blockDisjoint, h]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hscr
  obtain ⟨⟨lG, hG, hlG⟩, ⟨lY, hYs, hlY⟩, ⟨lQ, hQs, hlQ⟩, ⟨lR, hRs, hlR⟩⟩ := hscr
  obtain ⟨lA, hQas, hlA⟩ := hQa
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  -- the test loop
  obtain ⟨s₁, h₁, hsh₁, hfr₁, hG₁⟩ := exists_exec_deflate_testLoop (I := I) hsem p n k lo
    (if b then 0 else 1) hsG hSgG hsq (fun i j hi hj t ht => hSg _ (by
      have h1 : 2 * (lo + j) + (if b then 0 else 1) + 1 ≤ 2 * n := by split <;> omega
      have h2 := Nat.mul_le_mul_left n h1
      rw [Nat.mul_add, Nat.mul_one] at h2
      nlinarith)) hG (by omega)
  have hXG : s₁.store.readBlock p G 0 (k * k * 2) = some ((List.range (k * k * 2)).toArray.map
      fun w => (s₁.store.read p G (0 + w)).getD default) :=
    Store.readBlock_eq_some_map_range _ fun w hw => by
      obtain ⟨v, hv⟩ := hG₁ w (by omega)
      rw [zero_add, hv]
      rfl
  have hXP := (EntryLayout.holds_iff_readBlock_eq_some pairLayout s₁.store p Pm 0 Pmat).mp
    (hP.of_forall_read_eq fun i _ _ => hfr₁ p Pm i hPmG)
  -- the product
  have hk₁ := hmm.kcallStore_eq p (l := k) (m := k) (n := k) (a := (Pm, 0)) (b := (G, 0))
    (c := (Y, 0)) hXP hXG (hne (Ne.symm hPmY)) (hne (Ne.symm hGY))
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, I.kcallStore mm p [k, k, k] [(Pm, 0), (G, 0)] [(Y, 0)] s₁.store =
      some c₂ := by
    rw [hk₁]
    exact Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi => ⟨lY, hsh₁ ▸ hYs, by
      rw [EntryLayout.size_toArray] at hi
      change i < k * k * 2 at hi
      omega⟩
  have hYh := EntryLayout.holds_of_writeBlock_eq_some pairLayout (hk₁.symm.trans hc₂)
  have hsh₂ := (Interp.shape_of_kcallStore_eq_some hc₂).trans hsh₁
  -- the QR factorization
  have hk₂ := hqr.kcallStore_eq p (m := k) (n := k) (a := (Y, 0)) (q := (Qf, 0)) (r := (Rf, 0))
    ((EntryLayout.holds_iff_readBlock_eq_some pairLayout c₂ p Y 0 _).mp hYh) (hne hQfRf)
    (hne (Ne.symm hYQf)) (hne (Ne.symm hYRf))
  obtain ⟨c₃, hc₃⟩ : ∃ c₃, I.kcallStore qr p [k, k] [(Y, 0)] [(Qf, 0), (Rf, 0)] c₂ =
      some c₃ := by
    rw [hk₂]
    obtain ⟨c, hc⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := c₂) (b := Qf)
      (off := 0) (xs := pairLayout.toArray (qrR (pairLayout.toMatrix k k
        (pairLayout.toArray (mmR (pairLayout.toMatrix k k (pairLayout.toArray Pmat))
          (pairLayout.toMatrix k k ((List.range (k * k * 2)).toArray.map
            fun w => (s₁.store.read p G (0 + w)).getD default)))))).1)
      fun i hi => ⟨lQ, hsh₂ ▸ hQs, by
        rw [EntryLayout.size_toArray] at hi
        change i < k * k * 2 at hi
        omega⟩
    rw [hc, Option.bind_some]
    exact Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi =>
      ⟨lR, (Store.shape_of_writeBlock_eq_some hc).trans hsh₂ ▸ hRs, by
        rw [EntryLayout.size_toArray] at hi
        change i < k * k * 2 at hi
        omega⟩
  obtain ⟨hQf, -, hfr₃⟩ := hqr.holds_of_kcallStore_eq_some (fun _ => rfl) p (m := k) (n := k)
    (a := (Y, 0)) (q := (Qf, 0)) (r := (Rf, 0)) hYh (hne hQfRf) (hne (Ne.symm hYQf))
    (hne (Ne.symm hYRf)) hc₃
  have hsh₃ := (Interp.shape_of_kcallStore_eq_some hc₃).trans hsh₂
  -- the run
  change ∃ st', exec I (.seq (.loop _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) .skip)))) st = some st' ∧ _
  rw [exec_seq, h₁, Option.bind_some, exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
  rw [hc₂, Option.map_some, Option.bind_some, exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
  rw [hc₃, Option.map_some, Option.bind_some]
  exact exists_exec_zcopy_deflate p hr hQf (Ne.symm hQfQa) ⟨lA, hsh₃ ▸ hQas, hlA⟩
    (fun q b' i hb' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb'
      exact (hfr₃ q b' i (hne hb'.2.2.1) (hne hb'.2.2.2)).trans
        ((Store.read_of_writeBlock_eq_some_of_ne (hk₁.symm.trans hc₂) (Or.inl hb'.2.1)).trans
          (hfr₁ q b' i hb'.1))) hsh₃

/-- Deflation on stored samples succeeds under the standard model with every value in range,
if the kernels are routines on pairs and the buffers `G`, `Y`, `Qf`, `Rf` have $2n^2$ cells and the
block at `qo` of `Qa` fits (hypotheses on the inputs as `NLAlib.holds_of_exec_eighDeflateBlock`).
No printed source. -/
theorem exists_exec_eighDeflateBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n k r d lo : ℕ)
    (hk : lo + k ≤ n) (hr : r ≤ k) (b : Bool) {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ}
    {qo : IExp ℕ} {st : St P K C} {Pmat : Matrix (Fin k) (Fin k) (K × K)}
    (hP : pairLayout.Holds st.store p Pm 0 Pmat)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (hscr : ∀ X ∈ [G, Y, Qf, Rf], ∃ len, st.store.shape[X]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hQa : ∃ len, st.store.shape[Qa]? = some (p, len) ∧ qo.eval + 2 * (k * r) ≤ len) :
    ∃ st', exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
      (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st' := by
  exact (exists_exec_eighDeflateBlock_facts hmm hqr hsem p n k r d lo hk hr b hP hsq
    (fun w hw => ⟨_, hSg w hw⟩) hbufs hsqb hscr hQa).imp fun _ h => h.1

/-! ### The deflation as a routine specification -/

/-- A deflation modifies only its four scratch buffers (their first $2n^2$ cells) and its output
block, and keeps the tape positions, from every state. -/
theorem spec_eighDeflateBlock_frame {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n k r lo : ℕ) (hk : k ≤ n)
    (side : ℕ) (Sg : ℕ) (sq : Cell ℕ ℕ) (Pm G Y Qf Rf Qa : ℕ) (qo : IExp ℕ) :
    Spec .liberal I (fun _ => True) (eighDeflateBlock p mm qr (.const n) (.const k) (.const r)
        (.const lo) side Sg sq Pm G Y Qf Rf Qa qo).run
      [(G, 0, 2 * (n * n)), (Y, 0, 2 * (n * n)), (Qf, 0, 2 * (n * n)), (Rf, 0, 2 * (n * n)),
        matBlock Qa qo.eval k r 2] fun st st' => PosKept st st' := by
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hk hk
  have hc : ∀ a b : ℕ, a < k → b < k → ∀ t < 2, 0 ≤ 2 * (a + k * b) + t ∧
      2 * (a + k * b) + t < 0 + 2 * (n * n) := fun a b ha hb t ht => ⟨by omega, by nlinarith⟩
  refine Spec.seq_frame (Spec.loop_frame fun j hj => Spec.seq_frame (Spec.loop_frame fun i hi =>
    Spec.seq_frame (Spec.frame_of_mem (o := 0) (N := 2 * (n * n)) spec_bin_frame ?_
      List.mem_cons_self) (Spec.seq_frame (Spec.frame_of_mem (o := 0) (N := 2 * (n * n))
        spec_bin_frame ?_ List.mem_cons_self) spec_skip_frame)) spec_skip_frame)
    (Spec.seq_frame (Spec.frame_of_sub spec_kcall_frame ?_) (Spec.seq_frame
      (Spec.frame_of_sub spec_kcall_frame ?_) (Spec.seq_frame (Spec.named _ _ (Spec.seq_frame
        (Spec.loop_frame fun w hw => Spec.seq_frame (Spec.frame_of_mem (o := qo.eval)
          (N := k * r * 2) spec_copy_frame ?_ (by simp [matBlock])) spec_skip_frame)
          spec_skip_frame)) spec_skip_frame)))
  all_goals try simp only [IExp.eval_const] at hi hj
  all_goals try simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat] at hw
  · simpa [zidx] using hc i j hi hj 0 (by omega)
  · simpa [zidx, Nat.add_assoc] using hc i j hi hj 1 (by omega)
  · simp [hmm.2, mmShape, kcallBlocks, pairLayout]; omega
  · simp [hqr.2, qrShape, kcallBlocks, pairLayout]; omega
  · simp only [IExp.eval_add, IExp.eval_var]; omega

omit [Inhabited K] in
/-- A block holds at most one matrix. -/
private theorem pairLayout_holds_unique {s : Store P K} {p : P} {b off l m : ℕ}
    {Y Y' : Matrix (Fin l) (Fin m) (K × K)} (h : pairLayout.Holds s p b off Y)
    (h' : pairLayout.Holds s p b off Y') : Y = Y' := by
  ext i j
  · simpa [pairLayout] using (h i j ⟨0, two_pos⟩).symm.trans (h' i j ⟨0, two_pos⟩)
  · simpa [pairLayout] using (h i j ⟨1, one_lt_two⟩).symm.trans (h' i j ⟨1, one_lt_two⟩)

omit [Inhabited K] in
/-- A matrix stored as interleaved pairs reads only its block of `2` words per entry. -/
theorem readsOnly_pairLayoutHolds {l m : ℕ} (p : P) (b off : ℕ)
    (Y : Matrix (Fin l) (Fin m) (K × K)) :
    ReadsOnly (fun s : Store P K => pairLayout.Holds s p b off Y) [matBlock b off l m 2] :=
  readsOnly_entryLayoutHolds pairLayout p b off Y

/-- **The deflation as a routine specification**: if kernels `mm`, `qr` of `I` are the routines
`mmR`, `qrR` on interleaved pairs, then from a state holding the projector $\mathbf{P}$ at offset
$0$ of `Pm`, the stored $\sqrt{1/2}$ in the cell `sq` and initialised Gaussian words in `Sg`, the
run of `NLAlib.eighDeflateBlock` for a node of size $k$ at slot $lo$ (with $lo + k \le n$) and
rank $0 < r \le k$ modifies only its four scratch buffers and the block at `qo` of `Qa`, which then
holds a matrix, and keeps the tape positions. If the Gaussian words are the tape's words of depth
$d$, that matrix is `NLAlib.deflate M r P G` as in `NLAlib.holds_of_exec_eighDeflateBlock`; the
liberal mode assumes so. In mode `total` the run also succeeds, given the standard model on every
value, scratch buffers of $2n^2$ cells and the output block writable. No printed source. -/
theorem spec_eighDeflateBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ ∀ p x, safe p x))
    (p : P) (n k r d lo : ℕ) (hk : lo + k ≤ n) (hr : r ≤ k) (hr0 : 0 < r) (b : Bool)
    {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ} {qo : IExp ℕ} (Pmat : Matrix (Fin k) (Fin k) (K × K))
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa]) :
    let tape := fun s : Store P K => ∀ w < 4 * (n * n),
      s.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))
    RoutineSpec md I (fun st => pairLayout.Holds st.store p Pm 0 Pmat ∧
        st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p) ∧
        (∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v) ∧ (md = .liberal → tape st.store) ∧
        md.Needs ((∀ X ∈ [G, Y, Qf, Rf], ∃ len, st.store.shape[X]? = some (p, len) ∧
          2 * (n * n) ≤ len) ∧ Writable st.store p Qa qo.eval (k * r * 2)))
      (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo) (if b then 0 else 1)
        Sg sq Pm G Y Qf Rf Qa qo)
      [(G, 0, 2 * (n * n)), (Y, 0, 2 * (n * n)), (Qf, 0, 2 * (n * n)), (Rf, 0, 2 * (n * n)),
        matBlock Qa qo.eval k r 2]
      fun st st' => (∃ Q : Matrix (Fin k) (Fin r) (K × K),
        pairLayout.Holds st'.store p Qa qo.eval Q ∧ (tape st.store →
        Q = deflate (eighTapeMachine I p mmR qrR) r Pmat
          (leadingBlock k ((eighTapeSample n d lo).2 b)))) ∧ PosKept st st' := by
  intro tape
  have hfr := spec_eighDeflateBlock_frame hmm hqr p n k r lo (by omega) (if b then 0 else 1) Sg
    sq Pm G Y Qf Rf Qa qo
  have hval : ∀ st st', pairLayout.Holds st.store p Pm 0 Pmat →
      st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p) → exec I (eighDeflateBlock p mm
        qr (.const n) (.const k) (.const r) (.const lo) (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa
        qo).run st = some st' → ∀ Q : Matrix (Fin k) (Fin r) (K × K),
      pairLayout.Holds st'.store p Qa qo.eval Q → tape st.store → Q = deflate
        (eighTapeMachine I p mmR qrR) r Pmat (leadingBlock k ((eighTapeSample n d lo).2 b)) :=
    fun st st' hP hsq h Q hQ hSg => pairLayout_holds_unique hQ
      (holds_of_exec_eighDeflateBlock hmm hqr p n k r d lo hk hr b hP hsq hSg hbufs hsqb h).1
  have hrun : ∀ st, md = .total → pairLayout.Holds st.store p Pm 0 Pmat →
      st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p) →
      (∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v) →
      md.Needs ((∀ X ∈ [G, Y, Qf, Rf], ∃ len, st.store.shape[X]? = some (p, len) ∧
        2 * (n * n) ≤ len) ∧ Writable st.store p Qa qo.eval (k * r * 2)) →
      ∃ st', exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
        (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st' ∧
        ∃ Q : Matrix (Fin k) (Fin r) (K × K), pairLayout.Holds st'.store p Qa qo.eval Q := by
    rintro st rfl hP hsq hSg ⟨hscr, hW⟩
    obtain ⟨hs, hall⟩ := hsem
    obtain ⟨len, hl, hle⟩ := hW.exists_len (by have := Nat.mul_pos (by omega : 0 < k) hr0; omega)
    obtain ⟨st', h, hQ, -⟩ := exists_exec_eighDeflateBlock_facts hmm hqr
      (hs.mono_safe fun p x _ => hall p x) p n k r d lo hk hr b hP hsq hSg hbufs hsqb hscr
      ⟨len, hl, by linarith [Nat.mul_comm k r]⟩
    exact ⟨st', h, hQ⟩
  refine ⟨by exec_composable, Triple.of_exec (fun st ⟨hP, hsq, hSg, _, hN⟩ => ?_)
    fun st st' ⟨hP, hsq, hSg, hT, hN⟩ h => ⟨(hfr st trivial st' h).1, ?_, (hfr st trivial st' h).2⟩⟩
  · cases md
    · obtain ⟨st', h, -⟩ := hrun st rfl hP hsq hSg hN
      exact ⟨st', h⟩
    · trivial
  · cases md
    · obtain ⟨st'', h', Q, hQ⟩ := hrun st rfl hP hsq hSg hN
      rw [h] at h'
      cases h'
      exact ⟨Q, hQ, hval st st' hP hsq h Q hQ⟩
    · exact ⟨_, (holds_of_exec_eighDeflateBlock hmm hqr p n k r d lo hk hr b hP hsq (hT rfl) hbufs
        hsqb h).1, fun _ => rfl⟩

end NLAlib
